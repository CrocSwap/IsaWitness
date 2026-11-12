import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0146
import ArmFull.Fn.M0934
import ArmFull.Fn.M0935

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

def decode_sminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) minimum (Sail.Int.toNatChecked (n)) is_unsigned)


def decode_umaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) minimum (Sail.Int.toNatChecked (n)) is_unsigned)


def decode_uminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) minimum (Sail.Int.toNatChecked (n)) is_unsigned)


def decode_smaxv_advsimd_aarch64_instrs_vector_reduce_int_max (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((size +++ Q) == 0b100#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
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
  let min : Bool := (op == 1#1)
  (execute_aarch64_instrs_vector_reduce_int_max (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize)) min
    (Sail.Int.toNatChecked (n)) is_unsigned)


def decode_sminv_advsimd_aarch64_instrs_vector_reduce_int_max (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((size +++ Q) == 0b100#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
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
  let min : Bool := (op == 1#1)
  (execute_aarch64_instrs_vector_reduce_int_max (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize)) min
    (Sail.Int.toNatChecked (n)) is_unsigned)


def decode_umaxv_advsimd_aarch64_instrs_vector_reduce_int_max (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((size +++ Q) == 0b100#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
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
  let min : Bool := (op == 1#1)
  (execute_aarch64_instrs_vector_reduce_int_max (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize)) min
    (Sail.Int.toNatChecked (n)) is_unsigned)


def decode_uminv_advsimd_aarch64_instrs_vector_reduce_int_max (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((size +++ Q) == 0b100#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
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
  let min : Bool := (op == 1#1)
  (execute_aarch64_instrs_vector_reduce_int_max (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize)) min
    (Sail.Int.toNatChecked (n)) is_unsigned)


def decode_smlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  let sub_op : Bool := (o1 == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum (Sail.Int.toNatChecked (d))
    datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)) sub_op is_unsigned)


def decode_smlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  let sub_op : Bool := (o1 == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum (Sail.Int.toNatChecked (d))
    datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)) sub_op is_unsigned)


def decode_umlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  let sub_op : Bool := (o1 == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum (Sail.Int.toNatChecked (d))
    datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)) sub_op is_unsigned)


def decode_umlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  let sub_op : Bool := (o1 == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum (Sail.Int.toNatChecked (d))
    datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)) sub_op is_unsigned)


def decode_smlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4838) 0 7))) ) :
    SailM Nat )
  let Rmhi ← (( do (undefined_bitvector_at (← occLabel 4839) 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match size with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure ((Rmhi, index))))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure ((Rmhi, index))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index : Int := index
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (Rmhi +++ Rm))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  let is_unsigned : Bool := (U == 1#1)
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long (Sail.Int.toNatChecked (d))
    datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (idxdsize))
    (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (part)) sub_op is_unsigned)


def decode_smlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4840) 0 7))) ) :
    SailM Nat )
  let Rmhi ← (( do (undefined_bitvector_at (← occLabel 4841) 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match size with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure ((Rmhi, index))))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure ((Rmhi, index))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index : Int := index
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (Rmhi +++ Rm))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  let is_unsigned : Bool := (U == 1#1)
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long (Sail.Int.toNatChecked (d))
    datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (idxdsize))
    (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (part)) sub_op is_unsigned)


def decode_umlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4842) 0 7))) ) :
    SailM Nat )
  let Rmhi ← (( do (undefined_bitvector_at (← occLabel 4843) 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match size with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure ((Rmhi, index))))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure ((Rmhi, index))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index : Int := index
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (Rmhi +++ Rm))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  let is_unsigned : Bool := (U == 1#1)
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long (Sail.Int.toNatChecked (d))
    datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (idxdsize))
    (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (part)) sub_op is_unsigned)


def decode_umlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4844) 0 7))) ) :
    SailM Nat )
  let Rmhi ← (( do (undefined_bitvector_at (← occLabel 4845) 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match size with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure ((Rmhi, index))))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure ((Rmhi, index))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index : Int := index
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (Rmhi +++ Rm))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  let is_unsigned : Bool := (U == 1#1)
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long (Sail.Int.toNatChecked (d))
    datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (idxdsize))
    (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (part)) sub_op is_unsigned)


def decode_smmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla (Rd : (BitVec 5)) (Rn : (BitVec 5)) (B : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveInt8MatMulExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let op1_unsigned ← (( do (undefined_bool_at (← occLabel 4846) ()) ) : SailM Bool )
  let op2_unsigned ← (( do (undefined_bool_at (← occLabel 4847) ()) ) : SailM Bool )
  let (op1_unsigned, op2_unsigned) ← (( do
    match (BitVec.setWidth 2 (B +++ U)) with
    | 0b00 =>
      (let op1_unsigned : Bool := false
      let op2_unsigned : Bool := false
      (pure ((op1_unsigned, op2_unsigned))))
    | 0b01 =>
      (let op1_unsigned : Bool := true
      let op2_unsigned : Bool := true
      (pure ((op1_unsigned, op2_unsigned))))
    | 0b10 =>
      (let op1_unsigned : Bool := true
      let op2_unsigned : Bool := false
      (pure ((op1_unsigned, op2_unsigned))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × Bool) )
  let op2_unsigned := op2_unsigned
  let op1_unsigned := op1_unsigned
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat Rd)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned
    op2_unsigned)


def decode_ummla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla (Rd : (BitVec 5)) (Rn : (BitVec 5)) (B : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveInt8MatMulExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let op1_unsigned ← (( do (undefined_bool_at (← occLabel 4848) ()) ) : SailM Bool )
  let op2_unsigned ← (( do (undefined_bool_at (← occLabel 4849) ()) ) : SailM Bool )
  let (op1_unsigned, op2_unsigned) ← (( do
    match (BitVec.setWidth 2 (B +++ U)) with
    | 0b00 =>
      (let op1_unsigned : Bool := false
      let op2_unsigned : Bool := false
      (pure ((op1_unsigned, op2_unsigned))))
    | 0b01 =>
      (let op1_unsigned : Bool := true
      let op2_unsigned : Bool := true
      (pure ((op1_unsigned, op2_unsigned))))
    | 0b10 =>
      (let op1_unsigned : Bool := true
      let op2_unsigned : Bool := false
      (pure ((op1_unsigned, op2_unsigned))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × Bool) )
  let op2_unsigned := op2_unsigned
  let op1_unsigned := op1_unsigned
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat Rd)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned
    op2_unsigned)


def decode_usmmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla (Rd : (BitVec 5)) (Rn : (BitVec 5)) (B : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveInt8MatMulExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let op1_unsigned ← (( do (undefined_bool_at (← occLabel 4850) ()) ) : SailM Bool )
  let op2_unsigned ← (( do (undefined_bool_at (← occLabel 4851) ()) ) : SailM Bool )
  let (op1_unsigned, op2_unsigned) ← (( do
    match (BitVec.setWidth 2 (B +++ U)) with
    | 0b00 =>
      (let op1_unsigned : Bool := false
      let op2_unsigned : Bool := false
      (pure ((op1_unsigned, op2_unsigned))))
    | 0b01 =>
      (let op1_unsigned : Bool := true
      let op2_unsigned : Bool := true
      (pure ((op1_unsigned, op2_unsigned))))
    | 0b10 =>
      (let op1_unsigned : Bool := true
      let op2_unsigned : Bool := false
      (pure ((op1_unsigned, op2_unsigned))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × Bool) )
  let op2_unsigned := op2_unsigned
  let op1_unsigned := op1_unsigned
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat Rd)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned
    op2_unsigned)


def decode_smov_advsimd_aarch64_instrs_vector_transfer_integer_move_signed (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let size : Int := 0
  let b__0 := (Q +++ imm5)
  let size ← (( do
    if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (1#1 : (BitVec 1))) : Bool)
    then (pure (0))
    else
      (do
        if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 1 0)) == (0b10#2 : (BitVec 2))) : Bool)
        then (pure (1))
        else
          (do
            if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 5 5)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                     b__0 2 0)) == (0b100#3 : (BitVec 3)))) : Bool)
            then (pure (2))
            else sailThrow ((Error_Undefined ())))) ) : SailM Int )
  let size : Int := size
  let idxdsize : Int :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm5 4)])) == 1#1) : Bool)
    then 128
    else 64
  let index : Int :=
    (BitVec.toNat (Sail.BitVec.extractLsb imm5 4 (Sail.Int.toNatChecked ((size +i 1)))))
  let esize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (size)))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 64
    else 32
  ArmFull.assert (((esize == 8) || (esize == 16)) || (esize == 32)) "sail-arm/instrs64.sail:46177.44-46177.45"
  (execute_aarch64_instrs_vector_transfer_integer_move_signed (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (idxdsize)) index (Sail.Int.toNatChecked (n)))


def decode_smull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product (Sail.Int.toNatChecked (d))
    datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)) is_unsigned)


def decode_umull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product (Sail.Int.toNatChecked (d))
    datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)) is_unsigned)


def decode_smull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4858) 0 7))) ) :
    SailM Nat )
  let Rmhi ← (( do (undefined_bitvector_at (← occLabel 4859) 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match size with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure ((Rmhi, index))))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure ((Rmhi, index))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index : Int := index
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (Rmhi +++ Rm))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_long (Sail.Int.toNatChecked (d))
    datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (idxdsize))
    (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (part)) is_unsigned)


def decode_umull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4860) 0 7))) ) :
    SailM Nat )
  let Rmhi ← (( do (undefined_bitvector_at (← occLabel 4861) 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match size with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure ((Rmhi, index))))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure ((Rmhi, index))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index : Int := index
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (Rmhi +++ Rm))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_long (Sail.Int.toNatChecked (d))
    datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (idxdsize))
    (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (part)) is_unsigned)


def decode_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let neg : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) neg)


end ArmFull.Functions
