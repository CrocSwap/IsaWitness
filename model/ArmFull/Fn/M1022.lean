import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0087
import ArmFull.Fn.M0936
import ArmFull.Fn.M0937

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ConcurrencyInterfaceV1

namespace ArmFull

variable {real : Type} [Sail.SailReal real]

open ConcurrencyInterfaceV1

namespace Functions

open signal
open option
open exception
open arm_acc_type
open __InstrEnc
open WFxType
open VFPNegMul
open VCGTtype
open VCGEType
open VBitOps
open VBitOp
open VARange
open Unpredictable
open TranslationStage
open TimeStamp
open TMFailure
open TLBIOp
open TLBIMemAttr
open TLBILevel
open TGx
open SystemHintOp
open Signal
open ShiftType
open Shareability
open SecurityState
open SVECmp
open SRType
open SMEExceptionType
open SDFType
open RestrictType
open Register
open Regime
open ReduceOp
open PrivilegeLevel
open PrefetchHint
open PSTATEField
open PGSe
open PASpace
open PARTIDspaceType
open OpType
open MoveWideOp
open MemType
open MemTagType
open MemOp
open MemAtomicOp
open MOPSStage
open MBReqTypes
open MBReqDomain
open LogicalOp
open InterruptID
open InstrSet
open ImmediateOp
open GPCF
open GCSInstruction
open Feature
open Fault
open FPUnaryOp
open FPType
open FPRounding
open FPMaxMinOp
open FPExc
open FPConvOp
open ExtendType
open ExceptionalOccurrenceTargetState
open Exception
open ErrorState
open DeviceType
open DescriptorType
open DSBAlias
open CrossTriggerIn
open CountOp
open Constraint
open CompareOp
open CacheType
open CachePASpace
open CacheOpScope
open CacheOp
open BranchType
open BarrierExt
open Barrier
open ArchVersion
open AccessType
open ATAccess

def decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (_shl_int_general 8 (HighestSetBit immh))
  let datasize : Int := esize
  let elements : Nat := 1
  let part : Nat := 0
  let shift : Int := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
  let round : Bool := (op == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  ArmFull.assert ((((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) && (((((datasize == 4) || (datasize == 8)) || (datasize == 16)) || (datasize == 32)) || (datasize == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:48639.87-48639.88"
  (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) part round shift is_unsigned)


def decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then sailThrow ((Error_See "asimdimm"))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (_shl_int_general 8 (HighestSetBit immh))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (fdiv_int datasize esize)
  let shift : Int := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
  let round : Bool := (op == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  ArmFull.assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:48672.51-48672.52"
  (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Sail.Int.toNatChecked (d))
    datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (part)) round shift is_unsigned)


def decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (_shl_int_general 8 (HighestSetBit immh))
  let datasize : Int := esize
  let elements : Nat := 1
  let part : Nat := 0
  let shift : Int := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
  let round : Bool := (op == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  ArmFull.assert ((((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) && (((((datasize == 4) || (datasize == 8)) || (datasize == 16)) || (datasize == 32)) || (datasize == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:48706.87-48706.88"
  (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) part round shift is_unsigned)


def decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then sailThrow ((Error_See "asimdimm"))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (_shl_int_general 8 (HighestSetBit immh))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (fdiv_int datasize esize)
  let shift : Int := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
  let round : Bool := (op == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  ArmFull.assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:48739.51-48739.52"
  (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Sail.Int.toNatChecked (d))
    datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (part)) round shift is_unsigned)


def decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (_shl_int_general 8 (HighestSetBit immh))
  let datasize : Int := esize
  let elements : Nat := 1
  let part : Nat := 0
  let shift : Int := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
  let round : Bool := (op == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  ArmFull.assert ((((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) && (((((datasize == 4) || (datasize == 8)) || (datasize == 16)) || (datasize == 32)) || (datasize == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:48773.87-48773.88"
  (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) part round shift is_unsigned)


def decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then sailThrow ((Error_See "asimdimm"))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (_shl_int_general 8 (HighestSetBit immh))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (fdiv_int datasize esize)
  let shift : Int := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
  let round : Bool := (op == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  ArmFull.assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:48806.51-48806.52"
  (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Sail.Int.toNatChecked (d))
    datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (part)) round shift is_unsigned)


def decode_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (_shl_int_general 8 (HighestSetBit immh))
  let datasize : Int := esize
  let elements : Nat := 1
  let part : Nat := 0
  let shift : Int := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
  let round : Bool := (op == 1#1)
  ArmFull.assert ((((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) && (((((datasize == 4) || (datasize == 8)) || (datasize == 16)) || (datasize == 32)) || (datasize == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:48866.87-48866.88"
  (execute_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) part round shift)


def decode_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then sailThrow ((Error_See "asimdimm"))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (_shl_int_general 8 (HighestSetBit immh))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (fdiv_int datasize esize)
  let shift : Int := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
  let round : Bool := (op == 1#1)
  ArmFull.assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:48897.51-48897.52"
  (execute_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd (Sail.Int.toNatChecked (d))
    datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (part)) round shift)


def decode_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (_shl_int_general 8 (HighestSetBit immh))
  let datasize : Int := esize
  let elements : Nat := 1
  let part : Nat := 0
  let shift : Int := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
  let round : Bool := (op == 1#1)
  ArmFull.assert ((((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) && (((((datasize == 4) || (datasize == 8)) || (datasize == 16)) || (datasize == 32)) || (datasize == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:48929.87-48929.88"
  (execute_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) part round shift)


def decode_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then sailThrow ((Error_See "asimdimm"))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (_shl_int_general 8 (HighestSetBit immh))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (fdiv_int datasize esize)
  let shift : Int := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
  let round : Bool := (op == 1#1)
  ArmFull.assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:48960.51-48960.52"
  (execute_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd (Sail.Int.toNatChecked (d))
    datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (part)) round shift)


def decode_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (_shl_int_general 8 (HighestSetBit immh))
  let datasize : Int := esize
  let elements : Nat := 1
  let shift : Int := ((BitVec.toNat (immh +++ immb)) -i esize)
  let src_unsigned ← (( do (undefined_bool_at (← occLabel 4951) ()) ) : SailM Bool )
  let dst_unsigned ← (( do (undefined_bool_at (← occLabel 4952) ()) ) : SailM Bool )
  let (dst_unsigned, src_unsigned) ← (( do
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => sailThrow ((Error_Undefined ()))
    | 0b01 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := true
      (pure ((dst_unsigned, src_unsigned))))
    | 0b10 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := false
      (pure ((dst_unsigned, src_unsigned))))
    | _ =>
      (let src_unsigned : Bool := true
      let dst_unsigned : Bool := true
      (pure ((dst_unsigned, src_unsigned)))) ) : SailM (Bool × Bool) )
  let dst_unsigned := dst_unsigned
  let src_unsigned := src_unsigned
  ArmFull.assert ((((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((((((datasize == 4) || (datasize == 8)) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:49036.92-49036.93"
  (execute_aarch64_instrs_vector_shift_left_sat_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) dst_unsigned elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) shift src_unsigned)


def decode_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then sailThrow ((Error_See "asimdimm"))
  else (pure (()))
  if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (_shl_int_general 8 (HighestSetBit immh))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (fdiv_int datasize esize)
  let shift : Int := ((BitVec.toNat (immh +++ immb)) -i esize)
  let src_unsigned ← (( do (undefined_bool_at (← occLabel 4953) ()) ) : SailM Bool )
  let dst_unsigned ← (( do (undefined_bool_at (← occLabel 4954) ()) ) : SailM Bool )
  let (dst_unsigned, src_unsigned) ← (( do
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => sailThrow ((Error_Undefined ()))
    | 0b01 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := true
      (pure ((dst_unsigned, src_unsigned))))
    | 0b10 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := false
      (pure ((dst_unsigned, src_unsigned))))
    | _ =>
      (let src_unsigned : Bool := true
      let dst_unsigned : Bool := true
      (pure ((dst_unsigned, src_unsigned)))) ) : SailM (Bool × Bool) )
  let dst_unsigned := dst_unsigned
  let src_unsigned := src_unsigned
  ArmFull.assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:49087.51-49087.52"
  (execute_aarch64_instrs_vector_shift_left_sat_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) dst_unsigned elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) shift src_unsigned)


def decode_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (_shl_int_general 8 (HighestSetBit immh))
  let datasize : Int := esize
  let elements : Nat := 1
  let shift : Int := ((BitVec.toNat (immh +++ immb)) -i esize)
  let src_unsigned ← (( do (undefined_bool_at (← occLabel 4955) ()) ) : SailM Bool )
  let dst_unsigned ← (( do (undefined_bool_at (← occLabel 4956) ()) ) : SailM Bool )
  let (dst_unsigned, src_unsigned) ← (( do
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => sailThrow ((Error_Undefined ()))
    | 0b01 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := true
      (pure ((dst_unsigned, src_unsigned))))
    | 0b10 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := false
      (pure ((dst_unsigned, src_unsigned))))
    | _ =>
      (let src_unsigned : Bool := true
      let dst_unsigned : Bool := true
      (pure ((dst_unsigned, src_unsigned)))) ) : SailM (Bool × Bool) )
  let dst_unsigned := dst_unsigned
  let src_unsigned := src_unsigned
  ArmFull.assert ((((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((((((datasize == 4) || (datasize == 8)) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:49136.92-49136.93"
  (execute_aarch64_instrs_vector_shift_left_sat_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) dst_unsigned elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) shift src_unsigned)


def decode_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then sailThrow ((Error_See "asimdimm"))
  else (pure (()))
  if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (_shl_int_general 8 (HighestSetBit immh))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (fdiv_int datasize esize)
  let shift : Int := ((BitVec.toNat (immh +++ immb)) -i esize)
  let src_unsigned ← (( do (undefined_bool_at (← occLabel 4957) ()) ) : SailM Bool )
  let dst_unsigned ← (( do (undefined_bool_at (← occLabel 4958) ()) ) : SailM Bool )
  let (dst_unsigned, src_unsigned) ← (( do
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => sailThrow ((Error_Undefined ()))
    | 0b01 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := true
      (pure ((dst_unsigned, src_unsigned))))
    | 0b10 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := false
      (pure ((dst_unsigned, src_unsigned))))
    | _ =>
      (let src_unsigned : Bool := true
      let dst_unsigned : Bool := true
      (pure ((dst_unsigned, src_unsigned)))) ) : SailM (Bool × Bool) )
  let dst_unsigned := dst_unsigned
  let src_unsigned := src_unsigned
  ArmFull.assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:49187.51-49187.52"
  (execute_aarch64_instrs_vector_shift_left_sat_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) dst_unsigned elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) shift src_unsigned)


def decode_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (_shl_int_general 8 (HighestSetBit immh))
  let datasize : Int := esize
  let elements : Nat := 1
  let shift : Int := ((BitVec.toNat (immh +++ immb)) -i esize)
  let src_unsigned ← (( do (undefined_bool_at (← occLabel 4959) ()) ) : SailM Bool )
  let dst_unsigned ← (( do (undefined_bool_at (← occLabel 4960) ()) ) : SailM Bool )
  let (dst_unsigned, src_unsigned) ← (( do
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => sailThrow ((Error_Undefined ()))
    | 0b01 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := true
      (pure ((dst_unsigned, src_unsigned))))
    | 0b10 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := false
      (pure ((dst_unsigned, src_unsigned))))
    | _ =>
      (let src_unsigned : Bool := true
      let dst_unsigned : Bool := true
      (pure ((dst_unsigned, src_unsigned)))) ) : SailM (Bool × Bool) )
  let dst_unsigned := dst_unsigned
  let src_unsigned := src_unsigned
  ArmFull.assert ((((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((((((datasize == 4) || (datasize == 8)) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:49236.92-49236.93"
  (execute_aarch64_instrs_vector_shift_left_sat_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) dst_unsigned elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) shift src_unsigned)


def decode_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then sailThrow ((Error_See "asimdimm"))
  else (pure (()))
  if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (_shl_int_general 8 (HighestSetBit immh))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (fdiv_int datasize esize)
  let shift : Int := ((BitVec.toNat (immh +++ immb)) -i esize)
  let src_unsigned ← (( do (undefined_bool_at (← occLabel 4961) ()) ) : SailM Bool )
  let dst_unsigned ← (( do (undefined_bool_at (← occLabel 4962) ()) ) : SailM Bool )
  let (dst_unsigned, src_unsigned) ← (( do
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => sailThrow ((Error_Undefined ()))
    | 0b01 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := true
      (pure ((dst_unsigned, src_unsigned))))
    | 0b10 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := false
      (pure ((dst_unsigned, src_unsigned))))
    | _ =>
      (let src_unsigned : Bool := true
      let dst_unsigned : Bool := true
      (pure ((dst_unsigned, src_unsigned)))) ) : SailM (Bool × Bool) )
  let dst_unsigned := dst_unsigned
  let src_unsigned := src_unsigned
  ArmFull.assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:49287.51-49287.52"
  (execute_aarch64_instrs_vector_shift_left_sat_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) dst_unsigned elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) shift src_unsigned)


def decode_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let part : Nat := 0
  let elements : Nat := 1
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) part is_unsigned)


def decode_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd (Sail.Int.toNatChecked (d))
    datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (part)) is_unsigned)


def decode_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let part : Nat := 0
  let elements : Nat := 1
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) part is_unsigned)


def decode_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd (Sail.Int.toNatChecked (d))
    datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (part)) is_unsigned)


def decode_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let part : Nat := 0
  let elements : Nat := 1
  (execute_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) part)


def decode_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  (execute_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd (Sail.Int.toNatChecked (d))
    datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (part)))


def decode_srhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


end ArmFull.Functions
