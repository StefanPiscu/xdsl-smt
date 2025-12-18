from abc import abstractmethod, ABC
from dataclasses import dataclass

from xdsl.ir import Operation, SSAValue, Block, TypeAttribute

from xdsl_smt.dialects import smt_bitvector_dialect as smt_bv
from xdsl.dialects.smt import BitVectorType
from xdsl_smt.semantics.riscv_semantics import *

class IdDict:
    id = 0
    ids : Mapping[SSAValue, int] = {}
    def get_id(self, value: SSAValue) -> int:
        if value not in self.ids:
            self.ids[value] = self.id
            self.id = self.id + 1
        return self.ids[value]

def get_type(type : TypeAttribute) -> str:
    if isinstance(type, BitVectorType):
        return f"BitVec {type.width.data}"
    else: 
        raise ValueError(f"Cannot convert {type} to a lean type")

class LeanPrintable(ABC):
      
    @abstractmethod
    def print(self, op : Operation, ids : IdDict, indent=0) : pass

@dataclass
class BinaryOp(LeanPrintable):
    smt_op_type: type[Operation]
    lean_function_name: str

    def print(self, op : Operation, ids : IdDict, indent=0):
        assert type(op) == self.smt_op_type
        rtype = op.result_types[0]
        res, op1, op2 = op.results[0], op.operands[0], op.operands[1]
        print("{}let a{} : {} := ({} a{} a{}) ;".format(
            "  "*indent,
            ids.get_id(res),
            get_type(rtype),
            self.lean_function_name,
            ids.get_id(op1),
            ids.get_id(op2), 
        ))

@dataclass
class ExtendOp(LeanPrintable):

    mode : str 

    def print(self, op : Operation, ids : IdDict, indent=0):
        assert isinstance(rtype := op.result_types[0], BitVectorType)
        print("{}let a{} : {} := (BitVec.{}Extend {} a{}) ;".format(
            "  "*indent,
            ids.get_id(op.results[0]),
            get_type(rtype),
            self.mode,
            rtype.width.data,
            ids.get_id(op.operands[0]),
        ))

op_printers = {
    smt_bv.AddOp : BinaryOp(smt_bv.AddOp, "BitVec.add"),
    smt_bv.OrOp : BinaryOp(smt_bv.OrOp, "BitVec.or"),
    smt_bv.AndOp : BinaryOp(smt_bv.AndOp, "BitVec.and"),
    smt_bv.XorOp : BinaryOp(smt_bv.XorOp, "BitVec.xor"),
    smt_bv.SignExtendOp : ExtendOp("sign"),
    smt_bv.ZeroExtendOp : ExtendOp("zero"),
}

def print_lean_theorem(name : str, block: Block, results: Sequence[SSAValue]) -> None:
    assert(len(results) == 1)
    ids = IdDict()
    typed_args = ""
    args = ""

    for arg in block.args:
        args += f"a{ids.get_id(arg)} "
        typed_args += f"(a{ids.get_id(arg)} : {get_type(arg.type)}) "

    print(f"def _{name} {typed_args}: {get_type(results[0].type)} :=")
    for op in block.walk():
        if type(op) not in op_printers:
            raise ValueError(f"Cannot print {type.name} in lean")
        op_printers[type(op)].print(op, ids, indent=1) 
    print(f"  a{ids.get_id(results[0])}")
    print(f"theorem {name}_eq {typed_args}: {name} {args}= _{name} {args}:= by bv_decide")