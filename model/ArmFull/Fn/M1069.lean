module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0968
public import ArmFull.Fn.M0969 set_option backward.proofsInPublic true @[expose] public section

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

def decode_umull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Nat := 64
      let part : Int := (BitVec.toNat Q)
      let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product
        (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))
        is_unsigned))


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
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM ((BitVec 1) × Nat) )
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
  (__ArmCertEndOfDecode ())
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
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM ((BitVec 1) × Nat) )
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
  (__ArmCertEndOfDecode ())
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
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) neg)


def decode_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((size +++ Q) == 0b110#3) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
      let neg : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) neg))


def decode_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let neg : Bool := (U == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) neg)


def decode_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((size +++ Q) == 0b110#3) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
      let neg : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) neg))


def decode_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let is_unsigned : Bool := (U == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        is_unsigned))


def decode_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let is_unsigned : Bool := (U == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
      let is_unsigned : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        is_unsigned))


def decode_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4876) 0 7))) ) :
    SailM Nat )
  let Rmhi ← (( do (undefined_bitvector_at (← occLabel 4877) 1) ) : SailM (BitVec 1) )
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
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index : Int := index
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (Rmhi +++ Rm))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let part : Nat := 0
  let sub_op : Bool := (o2 == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (idxdsize))
    (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) part
    sub_op)


def decode_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4878) 0 7))) ) :
    SailM Nat )
  let Rmhi ← (( do (undefined_bitvector_at (← occLabel 4879) 1) ) : SailM (BitVec 1) )
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
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index : Int := index
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (Rmhi +++ Rm))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  let sub_op : Bool := (o2 == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd
    (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (idxdsize)) (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)) sub_op)


def decode_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4880) 0 7))) ) :
    SailM Nat )
  let Rmhi ← (( do (undefined_bitvector_at (← occLabel 4881) 1) ) : SailM (BitVec 1) )
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
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index : Int := index
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (Rmhi +++ Rm))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let part : Nat := 0
  let sub_op : Bool := (o2 == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (idxdsize))
    (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) part
    sub_op)


def decode_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4882) 0 7))) ) :
    SailM Nat )
  let Rmhi ← (( do (undefined_bitvector_at (← occLabel 4883) 1) ) : SailM (BitVec 1) )
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
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index : Int := index
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (Rmhi +++ Rm))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  let sub_op : Bool := (o2 == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd
    (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (idxdsize)) (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)) sub_op)


def decode_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int := esize
      let elements : Nat := 1
      let part : Nat := 0
      let sub_op : Bool := (o1 == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) part
        sub_op))


def decode_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Nat := 64
      let part : Int := (BitVec.toNat Q)
      let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
      let sub_op : Bool := (o1 == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd
        (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))
        sub_op))


def decode_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int := esize
      let elements : Nat := 1
      let part : Nat := 0
      let sub_op : Bool := (o1 == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) part
        sub_op))


def decode_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Nat := 64
      let part : Int := (BitVec.toNat Q)
      let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
      let sub_op : Bool := (o1 == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd
        (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part))
        sub_op))


def decode_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size == 0b11#2) || (size == 0b00#2)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int := esize
      let elements : Nat := 1
      let rounding : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        rounding))


def decode_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size == 0b11#2) || (size == 0b00#2)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
      let rounding : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        rounding))


def decode_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size == 0b11#2) || (size == 0b00#2)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int := esize
      let elements : Nat := 1
      let rounding : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        rounding))


def decode_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size == 0b11#2) || (size == 0b00#2)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let datasize : Int :=
        if ((Q == 1#1) : Bool)
        then 128
        else 64
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
      let rounding : Bool := (U == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        rounding))


def decode_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (op : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4900) 0 7))) ) :
    SailM Nat )
  let Rmhi ← (( do (undefined_bitvector_at (← occLabel 4901) 1) ) : SailM (BitVec 1) )
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
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index : Int := index
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (Rmhi +++ Rm))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let round : Bool := (op == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (idxdsize)) (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) round)


end ArmFull.Functions
