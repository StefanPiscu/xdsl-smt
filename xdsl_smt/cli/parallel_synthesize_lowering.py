import argparse
import subprocess as sp
import tempfile
import os
import sys
import json
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from io import StringIO
from typing import Any, List

from xdsl.printer import Printer
from xdsl.context import Context
from xdsl.parser import Parser
from xdsl.dialects.builtin import ModuleOp
from xdsl_smt.dialects import get_all_dialects

from xdsl_smt.cli.synthesize_lowering import get_input_operations, register_all_arguments



def worker_synthesize(op: ModuleOp, args: argparse.Namespace, size: int) -> dict[str, Any]:
    ctx = Context()
    ctx.allow_unregistered = True
    for name, factory in get_all_dialects().items():
        ctx.register_dialect(name, factory)

    in_io = StringIO()
    Printer(in_io, print_generic_format=True).print_op(op)
    input_str = in_io.getvalue()

    with tempfile.NamedTemporaryFile(mode="w", suffix=".mlir", delete=False) as tf:
        tf_name = tf.name
        tf.write(input_str)

    start_t = time.time()
    success = False
    out_str = None
    program_count = ""
    
    cmd = [
        "superoptimize", tf_name,
        f"--max-num-ops={size}",
        f"--dialect={args.output_dialect}",
        f"--configuration={args.output_configuration}",
    ]
    if args.opt: cmd.append("--opt")
    if args.synth_ops: cmd.append("--synth-ops")
    if args.count_programs: cmd.append("--count-programs")


    try:
        res = sp.run(
            cmd, capture_output=True, text=True, timeout=args.max_timeout
        )
        if res.returncode == 0:
            if args.count_programs:
                module, _, program_count = res.stdout.strip('\n').rpartition('\n')
            else: module = res.stdout
            parsed = Parser(ctx, module).parse_module()
            out_io = StringIO()
            Printer(out_io, print_generic_format=True).print_op(parsed)
            out_str = out_io.getvalue()
            success = True
        elif args.count_programs:
            _, _, program_count = res.stdout.strip('\n').rpartition('\n')
    except Exception as e:
        print(e, file=sys.stderr)
        success = False
    finally:
        if os.path.exists(tf_name):
            os.remove(tf_name)

    ret = {
        "size": size,
        "attempted_programs": None,
        "success": success,
        "duration_ms": round((time.time() - start_t) * 1000, 2),
        "input": input_str,
        "output": out_str
    }
    if args.count_programs: ret["attempted_programs"] = program_count
    return ret


def main():
    parser = argparse.ArgumentParser()
    register_all_arguments(parser)
    parser.add_argument("--threads", type=int, default=4, help="Number of threads")
    parser.add_argument("--max-timeout", type=float, default=None, help="Maximum timeout (s) for task")
    parser.add_argument(
        "--count-programs",
        dest="count_programs",
        help="Count the number of programs evaluated, print it at the end",
        action="store_true",
    )
    args = parser.parse_args()

    ctx = Context()
    ctx.allow_unregistered = True
    for name, factory in get_all_dialects().items():
        ctx.register_dialect(name, factory)

    worklist = get_input_operations(args, ctx)

    for size in range(1, args.max_num_ops + 1):
        if not worklist:
            break

        next_worklist : List[ModuleOp] = []
        with ThreadPoolExecutor(max_workers=args.threads) as executor:
            future_to_op = {
                executor.submit(worker_synthesize, op, args, size): op 
                for op in worklist
            }

            for future in as_completed(future_to_op):
                op = future_to_op[future]
                try:
                    res = future.result()
                    print(json.dumps(res))
                    sys.stdout.flush()
                    
                    if not res["success"]:
                        next_worklist.append(op)
                except Exception:
                    next_worklist.append(op)

        worklist = next_worklist

if __name__ == "__main__":
    main()