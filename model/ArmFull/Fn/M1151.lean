import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0086
import ArmFull.Fn.M0145
import ArmFull.Fn.M1105

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

def decode_fmls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_fused (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let sub_op : Bool := (op == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op)


def decode_fmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_mul_norounding_i_lower (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (S : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16MulNoRoundingToFP32Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (0#1 +++ Rm))
  if ((sz == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let index : Int := (BitVec.toNat ((H +++ L) +++ M))
  let esize : Nat := 32
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let sub_op : Bool := (S == 1#1)
  let part : Nat := 0
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_mul_norounding_i_lower
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) part
    sub_op)


def decode_fmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_mul_norounding_i_upper (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (S : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16MulNoRoundingToFP32Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (0#1 +++ Rm))
  if ((sz == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let index : Int := (BitVec.toNat ((H +++ L) +++ M))
  let esize : Nat := 32
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let sub_op : Bool := (S == 1#1)
  let part : Nat := 1
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_mul_norounding_i_lower
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) part
    sub_op)


def decode_fmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_mul_norounding_i_lower (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (S : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16MulNoRoundingToFP32Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (0#1 +++ Rm))
  if ((sz == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let index : Int := (BitVec.toNat ((H +++ L) +++ M))
  let esize : Nat := 32
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let sub_op : Bool := (S == 1#1)
  let part : Nat := 0
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_mul_norounding_i_lower
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) part
    sub_op)


def decode_fmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_mul_norounding_i_upper (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (S : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16MulNoRoundingToFP32Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (0#1 +++ Rm))
  if ((sz == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let index : Int := (BitVec.toNat ((H +++ L) +++ M))
  let esize : Nat := 32
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let sub_op : Bool := (S == 1#1)
  let part : Nat := 1
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_mul_norounding_i_lower
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) part
    sub_op)


def decode_fmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (S : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16MulNoRoundingToFP32Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((sz == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let sub_op : Bool := (S == 1#1)
  let part : Nat := 0
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) part sub_op)


def decode_fmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_mul_norounding_upper (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (S : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16MulNoRoundingToFP32Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((sz == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let sub_op : Bool := (S == 1#1)
  let part : Nat := 1
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) part sub_op)


def decode_fmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (S : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16MulNoRoundingToFP32Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((sz == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let sub_op : Bool := (S == 1#1)
  let part : Nat := 0
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) part sub_op)


def decode_fmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_mul_norounding_upper (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (S : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16MulNoRoundingToFP32Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((sz == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let sub_op : Bool := (S == 1#1)
  let part : Nat := 1
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) part sub_op)


def decode_fmul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_product (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_product
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_fmul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_product (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_product
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_fmul_float_aarch64_instrs_float_arithmetic_mul_product (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := 16
  let esize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure (16))
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let esize : Int := esize
  let negated : Bool := (op == 1#1)
  (execute_aarch64_instrs_float_arithmetic_mul_product (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) negated)


def decode_fnmul_float_aarch64_instrs_float_arithmetic_mul_product (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := 16
  let esize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure (16))
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let esize : Int := esize
  let negated : Bool := (op == 1#1)
  (execute_aarch64_instrs_float_arithmetic_mul_product (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) negated)


def decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat Rd)
  let index : Int := (BitVec.toNat ((H +++ L) +++ M))
  let esize : Nat := 16
  let datasize : Int := esize
  let elements : Nat := 1
  let mulx_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements esize (Sail.Int.toNatChecked (idxdsize))
    (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) mulx_op (Sail.Int.toNatChecked (n)))


def decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4290) 0 3))) ) :
    SailM Nat )
  let Rmhi : (BitVec 1) := M
  let b__0 := (sz +++ L)
  let index ← (( do
    if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 1 1)) == (0#1 : (BitVec 1))) : Bool)
    then
      (let index : Nat := (BitVec.toNat (H +++ L))
      (pure (index)))
    else
      (do
        match b__0 with
        | 0b10 =>
          (let index : Nat := (BitVec.toNat H)
          (pure (index)))
        | _ => sailThrow ((Error_Undefined ()))) ) : SailM Nat )
  let index : Int := index
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (Rmhi +++ Rm))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let mulx_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (idxdsize)) (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
    mulx_op (Sail.Int.toNatChecked (n)))


def decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat Rd)
  let index : Int := (BitVec.toNat ((H +++ L) +++ M))
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let mulx_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements esize (Sail.Int.toNatChecked (idxdsize))
    (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) mulx_op (Sail.Int.toNatChecked (n)))


def decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4291) 0 3))) ) :
    SailM Nat )
  let Rmhi : (BitVec 1) := M
  let b__0 := (sz +++ L)
  let index ← (( do
    if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 1 1)) == (0#1 : (BitVec 1))) : Bool)
    then
      (let index : Nat := (BitVec.toNat (H +++ L))
      (pure (index)))
    else
      (do
        match b__0 with
        | 0b10 =>
          (let index : Nat := (BitVec.toNat H)
          (pure (index)))
        | _ => sailThrow ((Error_Undefined ()))) ) : SailM Nat )
  let index : Int := index
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (Rmhi +++ Rm))
  if (((sz +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let mulx_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (idxdsize)) (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
    mulx_op (Sail.Int.toNatChecked (n)))


def decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat Rd)
  let index : Int := (BitVec.toNat ((H +++ L) +++ M))
  let esize : Nat := 16
  let datasize : Int := esize
  let elements : Nat := 1
  let mulx_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements esize (Sail.Int.toNatChecked (idxdsize))
    (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) mulx_op (Sail.Int.toNatChecked (n)))


def decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4292) 0 3))) ) :
    SailM Nat )
  let Rmhi : (BitVec 1) := M
  let b__0 := (sz +++ L)
  let index ← (( do
    if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 1 1)) == (0#1 : (BitVec 1))) : Bool)
    then
      (let index : Nat := (BitVec.toNat (H +++ L))
      (pure (index)))
    else
      (do
        match b__0 with
        | 0b10 =>
          (let index : Nat := (BitVec.toNat H)
          (pure (index)))
        | _ => sailThrow ((Error_Undefined ()))) ) : SailM Nat )
  let index : Int := index
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (Rmhi +++ Rm))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let mulx_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (idxdsize)) (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
    mulx_op (Sail.Int.toNatChecked (n)))


def decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat Rd)
  let index : Int := (BitVec.toNat ((H +++ L) +++ M))
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let mulx_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements esize (Sail.Int.toNatChecked (idxdsize))
    (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) mulx_op (Sail.Int.toNatChecked (n)))


def decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize : Int :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 4293) 0 3))) ) :
    SailM Nat )
  let Rmhi : (BitVec 1) := M
  let b__0 := (sz +++ L)
  let index ← (( do
    if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 1 1)) == (0#1 : (BitVec 1))) : Bool)
    then
      (let index : Nat := (BitVec.toNat (H +++ L))
      (pure (index)))
    else
      (do
        match b__0 with
        | 0b10 =>
          (let index : Nat := (BitVec.toNat H)
          (pure (index)))
        | _ => sailThrow ((Error_Undefined ()))) ) : SailM Nat )
  let index : Int := index
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (Rmhi +++ Rm))
  if (((sz +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let mulx_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (idxdsize)) (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
    mulx_op (Sail.Int.toNatChecked (n)))


def decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 16
  let datasize : Int := esize
  let elements : Nat := 1
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_extended_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_extended_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 16
  let datasize : Int := esize
  let elements : Nat := 1
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


end ArmFull.Functions
