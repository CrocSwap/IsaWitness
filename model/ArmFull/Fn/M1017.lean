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
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0218
import ArmFull.Fn.M0237
import ArmFull.Fn.M0257
import ArmFull.Fn.M0924
import ArmFull.Fn.M0932
import ArmFull.Fn.M0933

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

/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcgettag (n : Nat) (offset : (BitVec 64)) (t : Nat) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4439) 64) ) : SailM (BitVec 64) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) := (address + offset)
  let address : (BitVec 64) := (Align_bits address TAG_GRANULE)
  let accdesc ← (( do (CreateAccDescLDGSTG MemOp_LOAD) ) : SailM AccessDescriptor )
  let tag ← (( do (AArch64_MemTag_read address accdesc) ) : SailM (BitVec 4) )
  let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let w__3 ← (( do (AArch64_AddressWithAllocationTag w__2 tag) ) : SailM (BitVec 64) )
  (X_set t 64 w__3)


/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcgettagarray (n : Nat) (t : Nat) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let data : (BitVec 64) := (Zeros (n := 64))
  let address ← (( do (undefined_bitvector_at (← occLabel 4440) 64) ) : SailM (BitVec 64) )
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
  let accdesc ← (( do (CreateAccDescLDGSTG MemOp_LOAD) ) : SailM AccessDescriptor )
  let (address, data, index) ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Int := (count -i 1)
    (do
      let mut loop_vars := (address, data, index)
      for i in [loop_i_lower:loop_i_upper:1]i do
        let (address, data, index) := loop_vars
        loop_vars ← do
          let tag ← (( do (AArch64_MemTag_read address accdesc) ) : SailM (BitVec 4) )
          let index : Int := index
          ArmFull.assert ((0 ≤b (index *i 4)) && (((index *i 4) +i 3) <b 64)) "sail-arm/instrs64.sail:30614.72-30614.73"
          let data : (BitVec 64) :=
            (Sail.BitVec.updateSubrange data (Sail.Int.toNatChecked (((index *i 4) +i 3)))
              (Sail.Int.toNatChecked ((index *i 4))) (Sail.BitVec.castWidth tag))
          let address : (BitVec 64) := (BitVec.addInt address TAG_GRANULE)
          let index : Int := (index +i 1)
          (pure ((address, data, index)))
      (pure loop_vars)) ) : SailM ((BitVec 64) × (BitVec 64) × Int) )
  (X_set t 64 data)


def decode_mla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let sub_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op)


def decode_mls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let sub_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op)


def decode_mla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4654) 0 7))) ) :
    SailM Nat )
  let Rmhi ← (( do (undefined_bitvector_at (← occLabel 4655) 1) ) : SailM (BitVec 1) )
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
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (idxdsize)) (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) sub_op)


def decode_mls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4656) 0 7))) ) :
    SailM Nat )
  let Rmhi ← (( do (undefined_bitvector_at (← occLabel 4657) 1) ) : SailM (BitVec 1) )
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
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (idxdsize)) (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) sub_op)


def decode_mul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((U == 1#1) && (size != 0b00#2)) : Bool)
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
  let poly : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) poly)


def decode_pmul_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((U == 1#1) && (size != 0b00#2)) : Bool)
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
  let poly : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) poly)


def decode_mul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4671) 0 7))) ) :
    SailM Nat )
  let Rmhi ← (( do (undefined_bitvector_at (← occLabel 4672) 1) ) : SailM (BitVec 1) )
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
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_int (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (idxdsize)) (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)))


def decode_not_advsimd_aarch64_instrs_vector_arithmetic_unary_not (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 8
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) 8)
  (execute_aarch64_instrs_vector_arithmetic_unary_not (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (elements)) esize
    (Sail.Int.toNatChecked (n)))


def decode_pmull_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size == 0b01#2) || (size == 0b10#2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__1 ← (( do
    if (((size == 0b11#2) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do (HaveBit128PMULLExt ()) ) : SailM Bool )
        (pure (((! w__0) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly (Sail.Int.toNatChecked (d))
    datasize elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)))


def decode_rbit_advsimd_aarch64_instrs_vector_arithmetic_unary_rbit (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 8
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) 8)
  (execute_aarch64_instrs_vector_arithmetic_unary_rbit (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (elements)) esize
    (Sail.Int.toNatChecked (n)))


def decode_rev16_advsimd_aarch64_instrs_vector_arithmetic_unary_rev (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let op : (BitVec 2) := (o0 +++ U)
  if ((((BitVec.toNat op) +i (BitVec.toNat size)) ≥b 3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let container_size : Int := 16
  let container_size : Int :=
    match op with
    | 0b10 => 16
    | 0b01 => 32
    | 0b00 => 64
    | _ => container_size
  let container_size : Int := container_size
  let containers : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (container_size)))
  let elements_per_container : Int :=
    (Int.ediv (Sail.Int.toNatChecked (container_size)) (Sail.Int.toNatChecked (esize)))
  (execute_aarch64_instrs_vector_arithmetic_unary_rev containers (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements_per_container (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)))


def decode_rev32_advsimd_aarch64_instrs_vector_arithmetic_unary_rev (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let op : (BitVec 2) := (o0 +++ U)
  if ((((BitVec.toNat op) +i (BitVec.toNat size)) ≥b 3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let container_size : Int := 16
  let container_size : Int :=
    match op with
    | 0b10 => 16
    | 0b01 => 32
    | 0b00 => 64
    | _ => container_size
  let container_size : Int := container_size
  let containers : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (container_size)))
  let elements_per_container : Int :=
    (Int.ediv (Sail.Int.toNatChecked (container_size)) (Sail.Int.toNatChecked (esize)))
  (execute_aarch64_instrs_vector_arithmetic_unary_rev containers (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements_per_container (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)))


def decode_rev64_advsimd_aarch64_instrs_vector_arithmetic_unary_rev (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let op : (BitVec 2) := (o0 +++ U)
  if ((((BitVec.toNat op) +i (BitVec.toNat size)) ≥b 3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let container_size : Int := 16
  let container_size : Int :=
    match op with
    | 0b10 => 16
    | 0b01 => 32
    | 0b00 => 64
    | _ => container_size
  let container_size : Int := container_size
  let containers : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (container_size)))
  let elements_per_container : Int :=
    (Int.ediv (Sail.Int.toNatChecked (container_size)) (Sail.Int.toNatChecked (esize)))
  (execute_aarch64_instrs_vector_arithmetic_unary_rev containers (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements_per_container (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)))


def decode_rshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) : SailM Unit := do
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
  ArmFull.assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:41451.51-41451.52"
  (execute_aarch64_instrs_vector_shift_right_narrow_logical (Sail.Int.toNatChecked (d)) datasize
    elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (part)) round shift)


def decode_shrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) : SailM Unit := do
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
  ArmFull.assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64.sail:41483.51-41483.52"
  (execute_aarch64_instrs_vector_shift_right_narrow_logical (Sail.Int.toNatChecked (d)) datasize
    elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (part)) round shift)


def decode_saba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let accumulate : Bool := (ac == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_diff accumulate
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_sabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let accumulate : Bool := (ac == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_diff accumulate
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_uaba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let accumulate : Bool := (ac == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_diff accumulate
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_uabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let accumulate : Bool := (ac == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_diff accumulate
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_sabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let accumulate : Bool := (op == 0#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_diff accumulate
    (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))
    is_unsigned)


def decode_sabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let accumulate : Bool := (op == 0#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_diff accumulate
    (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))
    is_unsigned)


def decode_uabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let accumulate : Bool := (op == 0#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_diff accumulate
    (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))
    is_unsigned)


def decode_uabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let accumulate : Bool := (op == 0#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_diff accumulate
    (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))
    is_unsigned)


def decode_sadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked ((2 *i esize))))
  let acc : Bool := (op == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_add_pairwise acc (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) is_unsigned)


end ArmFull.Functions
