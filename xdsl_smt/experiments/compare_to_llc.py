import sys
import json
import argparse
import subprocess as sp
import tempfile
import os
import re
from io import StringIO
from typing import Dict, Any, Generator

from xdsl.context import Context
from xdsl.parser import Parser
from xdsl.printer import Printer
from xdsl.dialects.builtin import ModuleOp
from xdsl_smt.dialects import get_all_dialects
from xdsl_smt.utils.get_submodule_path import *

def run_tool_with_tempfile(cmd_base: list[str], input_text: str, out_arg : bool = False) -> str:
  with tempfile.NamedTemporaryFile(mode="w", delete=False, suffix=".mlir") as tmp:
    tmp.write(input_text)
    tmp_name = tmp.name
  try:
    cmd = cmd_base.copy()
    if out_arg:
       cmd.extend([tmp_name, "-o", "-"])
    else:
       cmd.extend([tmp_name])
    result = sp.run(cmd, capture_output=True, text=True, check=True)
    return result.stdout
  except sp.CalledProcessError as e:
    print(f"Tool failed: {' '.join(cmd_base)}\n{e.stderr}", file=sys.stderr)
    return ""
  finally:
    if os.path.exists(tmp_name):
        os.remove(tmp_name)

def count_assembly_instructions(asm_text: str) -> int:
    # Matches lines starting with whitespace and letters, but excludes 'mv', 'sd', 'ld' 
    # as we don't count the instructions related to register allocation, also excludes ret
    return sum(
        1 for line in asm_text.splitlines() 
        if re.match(r"^\s+[a-z]+", line) and not re.match(r"^\s+(mv|ret|sd|ld)\b", line)
    )

def count_xdsl_riscv_ops(mlir_text: str) -> int:
    # Matches an SSA assignment (e.g., "%0 = " or "%0, %1 = ") 
    # followed immediately by the riscv operation, with or without quotes.
    op_pattern = re.compile(r"^\s*(?:%[^=]+\=\s*)?\"?riscv\.[a-zA-Z0-9_]+\"?")
    return sum(1 for line in mlir_text.splitlines() if op_pattern.match(line))

def module_to_string(module: ModuleOp) -> str:
  out = StringIO()
  Printer(out, print_generic_format=True).print_op(module)
  return out.getvalue()

def clean_asm(asm_code: str):
    clean_lines = [line.strip() for line in asm_code.splitlines() if re.match(r"^\s+[a-z]+", line)]
    return "\n".join(clean_lines)

def evaluate_path_a_llvm(input_code: str) -> tuple[int, str]:
  mlir_opt_cmd = [get_llvm_executable_path("mlir-opt"), 
      "-convert-arith-to-llvm", 
      "-convert-func-to-llvm"
  ]
  llvm_dialect_code = run_tool_with_tempfile(mlir_opt_cmd, input_code)
  
  llvmir_code = run_tool_with_tempfile(
      [get_llvm_executable_path("mlir-translate"), "-mlir-to-llvmir"], 
      llvm_dialect_code
  )
  
  llc_cmd = ["llc", #the llvm-project in mlir-fuzz doesn't have riscv64 
      "-mtriple=riscv64", 
      "-mattr=+i,-m,-a,-f,-d,-c", 
      "-O0"
  ]
  asm_code = run_tool_with_tempfile(llc_cmd, llvmir_code, True)
  return count_assembly_instructions(asm_code), clean_asm(asm_code)

def evaluate_path_b_pdl(combined_code: str) -> int:
  passes = "apply-pdl"
  xdsl_out = run_tool_with_tempfile(["xdsl-opt", "-p", passes], combined_code)
  return count_xdsl_riscv_ops(xdsl_out)

def setup_context() -> Context:
  ctx = Context()
  ctx.allow_unregistered = True
  for name, thunk in get_all_dialects().items():
    ctx.register_dialect(name, thunk)
  return ctx

def process_evaluations(data_file: str, pdl_file: str) -> Generator[Dict[str, Any], None, None]:
  ctx = setup_context()

  with open(pdl_file, 'r') as f:
    pdl_module = Parser(ctx, f.read()).parse_module()

  with open(data_file, 'r') as f:
    for idx, line in enumerate(f):
      line = line.strip()
      if not line: continue
      data = json.loads(line)
      if not data.get("success"):
          continue

      input_module = Parser(ctx, data["input"]).parse_module()
      input_code_str = module_to_string(input_module)
      
      combined_module = pdl_module.clone()
      for op in input_module.body.blocks[0].ops:
          combined_module.body.blocks[0].add_op(op.clone())
      
      combined_code_str = module_to_string(combined_module)

      llvm_count, clean_asm = evaluate_path_a_llvm(input_code_str)
      xdsl_count = evaluate_path_b_pdl(combined_code_str)

      yield {
          "id": idx,
          "input_program": input_code_str,
          "parsed_asm": clean_asm,
          "llvm_instruction_count": llvm_count,
          "xdsl_riscv_ops_count": xdsl_count
      }

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('data_file', help="JSON lines file containing synthesis lowerings")
    parser.add_argument('pdl_file', help="MLIR file containing all generated PDL patterns")
    args = parser.parse_args()

    for res in process_evaluations(args.data_file, args.pdl_file):
        print(json.dumps(res))
        sys.stdout.flush()

if __name__ == "__main__":
    main()