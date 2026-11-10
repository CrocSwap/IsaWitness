import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0017
import ArmFull.Fn.M0044
import ArmFull.Fn.M0061
import ArmFull.Fn.M0087
import ArmFull.Fn.M0118
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0237
import ArmFull.Fn.M0257
import ArmFull.Fn.M0924
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

def decode_urhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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


def decode_sri_advsimd_aarch64_instrs_vector_shift_right_insert_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) != 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 3)
  let datasize : Int := esize
  let elements : Nat := 1
  let shift : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  (execute_aarch64_instrs_vector_shift_right_insert_sisd (Sail.Int.toNatChecked (d)) datasize
    elements esize (Sail.Int.toNatChecked (n)) shift)


def decode_sri_advsimd_aarch64_instrs_vector_shift_right_insert_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) : SailM Unit := do
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
  let shift : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  (execute_aarch64_instrs_vector_shift_right_insert_sisd (Sail.Int.toNatChecked (d)) datasize
    elements esize (Sail.Int.toNatChecked (n)) shift)


def decode_srshr_advsimd_aarch64_instrs_vector_shift_right_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) != 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 3)
  let datasize : Int := esize
  let elements : Nat := 1
  let shift : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate (Sail.Int.toNatChecked (d)) datasize
    elements esize (Sail.Int.toNatChecked (n)) round shift is_unsigned)


def decode_srshr_advsimd_aarch64_instrs_vector_shift_right_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let shift : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate (Sail.Int.toNatChecked (d)) datasize
    elements esize (Sail.Int.toNatChecked (n)) round shift is_unsigned)


def decode_srsra_advsimd_aarch64_instrs_vector_shift_right_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) != 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 3)
  let datasize : Int := esize
  let elements : Nat := 1
  let shift : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate (Sail.Int.toNatChecked (d)) datasize
    elements esize (Sail.Int.toNatChecked (n)) round shift is_unsigned)


def decode_srsra_advsimd_aarch64_instrs_vector_shift_right_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let shift : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate (Sail.Int.toNatChecked (d)) datasize
    elements esize (Sail.Int.toNatChecked (n)) round shift is_unsigned)


def decode_sshr_advsimd_aarch64_instrs_vector_shift_right_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) != 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 3)
  let datasize : Int := esize
  let elements : Nat := 1
  let shift : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate (Sail.Int.toNatChecked (d)) datasize
    elements esize (Sail.Int.toNatChecked (n)) round shift is_unsigned)


def decode_sshr_advsimd_aarch64_instrs_vector_shift_right_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let shift : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate (Sail.Int.toNatChecked (d)) datasize
    elements esize (Sail.Int.toNatChecked (n)) round shift is_unsigned)


def decode_ssra_advsimd_aarch64_instrs_vector_shift_right_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) != 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 3)
  let datasize : Int := esize
  let elements : Nat := 1
  let shift : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate (Sail.Int.toNatChecked (d)) datasize
    elements esize (Sail.Int.toNatChecked (n)) round shift is_unsigned)


def decode_ssra_advsimd_aarch64_instrs_vector_shift_right_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let shift : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate (Sail.Int.toNatChecked (d)) datasize
    elements esize (Sail.Int.toNatChecked (n)) round shift is_unsigned)


def decode_urshr_advsimd_aarch64_instrs_vector_shift_right_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) != 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 3)
  let datasize : Int := esize
  let elements : Nat := 1
  let shift : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate (Sail.Int.toNatChecked (d)) datasize
    elements esize (Sail.Int.toNatChecked (n)) round shift is_unsigned)


def decode_urshr_advsimd_aarch64_instrs_vector_shift_right_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let shift : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate (Sail.Int.toNatChecked (d)) datasize
    elements esize (Sail.Int.toNatChecked (n)) round shift is_unsigned)


def decode_ursra_advsimd_aarch64_instrs_vector_shift_right_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) != 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 3)
  let datasize : Int := esize
  let elements : Nat := 1
  let shift : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate (Sail.Int.toNatChecked (d)) datasize
    elements esize (Sail.Int.toNatChecked (n)) round shift is_unsigned)


def decode_ursra_advsimd_aarch64_instrs_vector_shift_right_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let shift : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate (Sail.Int.toNatChecked (d)) datasize
    elements esize (Sail.Int.toNatChecked (n)) round shift is_unsigned)


def decode_ushr_advsimd_aarch64_instrs_vector_shift_right_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) != 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 3)
  let datasize : Int := esize
  let elements : Nat := 1
  let shift : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate (Sail.Int.toNatChecked (d)) datasize
    elements esize (Sail.Int.toNatChecked (n)) round shift is_unsigned)


def decode_ushr_advsimd_aarch64_instrs_vector_shift_right_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let shift : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate (Sail.Int.toNatChecked (d)) datasize
    elements esize (Sail.Int.toNatChecked (n)) round shift is_unsigned)


def decode_usra_advsimd_aarch64_instrs_vector_shift_right_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) != 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 3)
  let datasize : Int := esize
  let elements : Nat := 1
  let shift : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate (Sail.Int.toNatChecked (d)) datasize
    elements esize (Sail.Int.toNatChecked (n)) round shift is_unsigned)


def decode_usra_advsimd_aarch64_instrs_vector_shift_right_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let shift : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate (Sail.Int.toNatChecked (d)) datasize
    elements esize (Sail.Int.toNatChecked (n)) round shift is_unsigned)


def decode_sshll_advsimd_aarch64_instrs_vector_shift_left_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let shift : Int := ((BitVec.toNat (immh +++ immb)) -i esize)
  let is_unsigned : Bool := (U == 1#1)
  ArmFull.assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:50352.51-50352.52"
  (execute_aarch64_instrs_vector_shift_left_long (Sail.Int.toNatChecked (d)) datasize elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)) shift
    is_unsigned)


def decode_ushll_advsimd_aarch64_instrs_vector_shift_left_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let shift : Int := ((BitVec.toNat (immh +++ immb)) -i esize)
  let is_unsigned : Bool := (U == 1#1)
  ArmFull.assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:50384.51-50384.52"
  (execute_aarch64_instrs_vector_shift_left_long (Sail.Int.toNatChecked (d)) datasize elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)) shift
    is_unsigned)


/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcsettagarray (n : Nat) (t : Nat) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let data ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let address ← (( do (undefined_bitvector_at (← occLabel 4995) 64) ) : SailM (BitVec 64) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let w__3 ← (( do readReg GMID_EL1 ) : SailM (BitVec 64) )
  let size : Nat :=
    (Sail.Int.toNatChecked ((4 *i (2 ^i (BitVec.toNat (_get_GMID_EL1_Type_BS w__3))))))
  let address : (BitVec 64) := (Align_bits address size)
  let count : Int := (Int.shiftr size LOG2_TAG_GRANULE)
  let index : Int :=
    (BitVec.toNat
      (Sail.BitVec.extractLsb address (Sail.Int.toNatChecked ((LOG2_TAG_GRANULE +i 3)))
        LOG2_TAG_GRANULE))
  let accdesc ← (( do (CreateAccDescLDGSTG MemOp_STORE) ) : SailM AccessDescriptor )
  let (address, index) ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Int := (count -i 1)
    (do
      let mut loop_vars := (address, index)
      for i in [loop_i_lower:loop_i_upper:1]i do
        let (address, index) := loop_vars
        loop_vars ← do
          let index : Int := index
          ArmFull.assert ((0 ≤b (index *i 4)) && (((index *i 4) +i 3) <b 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:50826.72-50826.73"
          let tag : (BitVec 4) :=
            (Sail.BitVec.castWidth (Sail.BitVec.extractLsb data
              (Sail.Int.toNatChecked (((index *i 4) +i 3))) (Sail.Int.toNatChecked ((index *i 4)))))
          (AArch64_MemTag_set address accdesc tag)
          let address : (BitVec 64) := (BitVec.addInt address TAG_GRANULE)
          let index : Int := (index +i 1)
          (pure ((address, index)))
      (pure loop_vars)) ) : SailM ((BitVec 64) × Int) )
  (pure (()))


def decode_sudot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (US : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveInt8MatMulExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let op1_unsigned : Bool := (US == 1#1)
  let op2_unsigned : Bool := (US == 0#1)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (M +++ Rm))
  let d : Int := (BitVec.toNat Rd)
  let i : Int := (BitVec.toNat (H +++ L))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) 32)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (i)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned)


def decode_usdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (US : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveInt8MatMulExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let op1_unsigned : Bool := (US == 1#1)
  let op2_unsigned : Bool := (US == 0#1)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (M +++ Rm))
  let d : Int := (BitVec.toNat Rd)
  let i : Int := (BitVec.toNat (H +++ L))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) 32)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (elements)) (Sail.Int.toNatChecked (i)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned)


def decode_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) is_unsigned)


def decode_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
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
  (execute_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) is_unsigned)


def decode_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) is_unsigned)


def decode_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
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
  (execute_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) is_unsigned)


def decode_tbl_advsimd_aarch64_instrs_vector_transfer_vector_table (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (len : (BitVec 2)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) 8)
  let regs : Int := ((BitVec.toNat len) +i 1)
  let is_tbl : Bool := (op == 0#1)
  (execute_aarch64_instrs_vector_transfer_vector_table (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (elements)) is_tbl
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)))


def decode_tbx_advsimd_aarch64_instrs_vector_transfer_vector_table (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (len : (BitVec 2)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) 8)
  let regs : Int := ((BitVec.toNat len) +i 1)
  let is_tbl : Bool := (op == 0#1)
  (execute_aarch64_instrs_vector_transfer_vector_table (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (elements)) is_tbl
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)))


def decode_trn1_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
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
  let part : Int := (BitVec.toNat op)
  let pairs : Int := (Int.ediv (Sail.Int.toNatChecked (elements)) 2)
  (execute_aarch64_instrs_vector_transfer_vector_permute_transpose (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) pairs (Sail.Int.toNatChecked (part)))


def decode_trn2_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
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
  let part : Int := (BitVec.toNat op)
  let pairs : Int := (Int.ediv (Sail.Int.toNatChecked (elements)) 2)
  (execute_aarch64_instrs_vector_transfer_vector_permute_transpose (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) pairs (Sail.Int.toNatChecked (part)))


end ArmFull.Functions
