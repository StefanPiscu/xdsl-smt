import sys
import json
import argparse
from typing import Generator
from dataclasses import dataclass

from xdsl.context import Context
from xdsl.parser import Parser
from xdsl.printer import Printer
from xdsl.ir import Operation, Block, Region, SSAValue, Attribute
from xdsl.dialects.builtin import ModuleOp, UnrealizedConversionCastOp
from xdsl.dialects import pdl
from xdsl.dialects.func import FuncOp
from xdsl_smt.dialects import get_all_dialects
from xdsl_smt.utils.pdl import func_to_pdl

@dataclass
class SynthesisResult:
    input_module: ModuleOp
    output_module: ModuleOp
    rewrite: pdl.PatternOp

def get_root_operation(module: ModuleOp) -> Operation:
    if not module.body.blocks:
        raise ValueError("Empty module")
    
    block = module.body.blocks[0]
    func = block.ops.first
    assert isinstance(func, FuncOp)
    Printer(sys.stdout).print_region(func_to_pdl(func)[0])
    op = func.body.block.ops.first
    assert isinstance(op, Operation)
    return op

def get_func_op(module: ModuleOp) -> FuncOp:
    block = module.body.blocks[0]
    func = block.ops.first
    assert isinstance(func, FuncOp)
    return func
def generate_pdl_pattern(input_module: ModuleOp, output_module: ModuleOp, name: str = "lowering") -> pdl.PatternOp:
    src_op = get_func_op(input_module)
    pdl_pattern, args, root, _ = func_to_pdl(src_op)

    body = Region()
    block = Block()
    body.add_block(block)
    
    for op in pdl_pattern.walk():
        op.detach()
        block.add_op(op)
    
    dst_op = get_func_op(output_module)
    rewrite_region = Region()
    rewrite_block = Block()
    rewrite_region.add_block(rewrite_block)

    def create_cast(val: SSAValue, target_type: Attribute) -> SSAValue:
        type_op = pdl.TypeOp(target_type)
        rewrite_block.add_op(type_op)
        
        cast_op = pdl.OperationOp(
            op_name= UnrealizedConversionCastOp.name,
            operand_values=[val],
            type_values=[type_op.results[0]]
        )
        rewrite_block.add_op(cast_op)
        
        res_op = pdl.ResultOp(
            index = 0,
            parent = cast_op.results[0]
        )
        rewrite_block.add_op(res_op)
        return res_op.results[0]

    dst_input_types = dst_op.function_type.inputs.data
    assert len(args) == len(dst_input_types)
    casted_args = [create_cast(arg, dtype) for arg, dtype in zip(args, dst_input_types)]

    pdl_rewrite, _, _, res = func_to_pdl(dst_op, arguments=casted_args) 

    for op in pdl_rewrite.walk():
        op.detach()
        rewrite_block.add_op(op)

    src_output_types = src_op.function_type.outputs.data
    assert len(res) == len(src_output_types)
    casted_res = [create_cast(r, stype) for r, stype in zip(res, src_output_types)]

    assert isinstance(root, SSAValue)
    replace_op = pdl.ReplaceOp(root, repl_values=casted_res)
    rewrite_block.add_op(replace_op)

    rewrite_op = pdl.RewriteOp(root, rewrite_region)
    block.add_op(rewrite_op)

    return pdl.PatternOp(benefit=1, sym_name=None, body=body)

def process_lowering(input_file: str) -> Generator[SynthesisResult, None, None]:
    ctx = Context()
    ctx.allow_unregistered = True
    for name, thunk in get_all_dialects().items():
        ctx.register_dialect(name, thunk)

    input = open(input_file, 'r')

    count = 0
    for line in input:
        line = line.strip()
        if not line: continue
        data = json.loads(line)

        if data.get("success"):
            input_module = Parser(ctx, data["input"]).parse_module()
            output_module = Parser(ctx, data["output"]).parse_module()
            
            pattern = generate_pdl_pattern(
                    input_module, 
                    output_module, 
                    name=f"generated_rewrite_{count}"
            )
            
            yield SynthesisResult(input_module, output_module, pattern)
            count += 1
    input.close()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('input_file')
    args = parser.parse_args()

    pdl_module = ModuleOp([])
    results = process_lowering(args.input_file)
    
    for res in results:
        if pdl_module.body.blocks:
            pdl_module.body.blocks[0].add_op(res.rewrite)
    
    Printer(sys.stdout).print_op(pdl_module) # type: ignore

if __name__ == "__main__":
    main()