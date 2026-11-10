import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0087
import ArmFull.Fn.M0145
import ArmFull.Fn.M0933
import ArmFull.Fn.M0934

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

def decode_saddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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


def decode_uadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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


def decode_uaddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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


def decode_saddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long
    (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)) sub_op
    is_unsigned)


def decode_ssubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long
    (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)) sub_op
    is_unsigned)


def decode_uaddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long
    (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)) sub_op
    is_unsigned)


def decode_usubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long
    (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)) sub_op
    is_unsigned)


def decode_saddlv_advsimd_aarch64_instrs_vector_reduce_add_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_reduce_add_long (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) is_unsigned)


def decode_uaddlv_advsimd_aarch64_instrs_vector_reduce_add_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_reduce_add_long (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) is_unsigned)


def decode_saddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide
    (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)) sub_op
    is_unsigned)


def decode_ssubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide
    (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)) sub_op
    is_unsigned)


def decode_uaddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide
    (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)) sub_op
    is_unsigned)


def decode_usubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide
    (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)) sub_op
    is_unsigned)


def decode_sdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveDOTPExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size != 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let is_signed : Bool := (U == 0#1)
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_signed)


def decode_udot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveDOTPExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size != 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let is_signed : Bool := (U == 0#1)
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_signed)


def decode_sdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveDOTPExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size != 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let is_signed : Bool := (U == 0#1)
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (M +++ Rm))
  let index : Int := (BitVec.toNat (H +++ L))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  (execute_aarch64_instrs_vector_arithmetic_binary_element_dotp (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_signed)


def decode_udot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveDOTPExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size != 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let is_signed : Bool := (U == 0#1)
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (M +++ Rm))
  let index : Int := (BitVec.toNat (H +++ L))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  (execute_aarch64_instrs_vector_arithmetic_binary_element_dotp (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_signed)


def decode_shadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_uhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_shl_advsimd_aarch64_instrs_vector_shift_left_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) != 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 3)
  let datasize : Int := esize
  let elements : Nat := 1
  let shift : Int := ((BitVec.toNat (immh +++ immb)) -i esize)
  (execute_aarch64_instrs_vector_shift_left_sisd (Sail.Int.toNatChecked (d)) datasize elements esize
    (Sail.Int.toNatChecked (n)) shift)


def decode_shl_advsimd_aarch64_instrs_vector_shift_left_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_shift_left_sisd (Sail.Int.toNatChecked (d)) datasize elements esize
    (Sail.Int.toNatChecked (n)) shift)


def decode_shll_advsimd_aarch64_instrs_vector_arithmetic_unary_shift (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  let shift : Int := esize
  let is_unsigned : Bool := false
  (execute_aarch64_instrs_vector_arithmetic_unary_shift (Sail.Int.toNatChecked (d)) datasize
    elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (part)) (Sail.Int.toNatChecked (shift)) is_unsigned)


def decode_shsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned)


def decode_uhsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned)


def decode_sli_advsimd_aarch64_instrs_vector_shift_left_insert_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) != 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 3)
  let datasize : Int := esize
  let elements : Nat := 1
  let shift : Int := ((BitVec.toNat (immh +++ immb)) -i esize)
  (execute_aarch64_instrs_vector_shift_left_insert_sisd (Sail.Int.toNatChecked (d)) datasize
    elements esize (Sail.Int.toNatChecked (n)) shift)


def decode_sli_advsimd_aarch64_instrs_vector_shift_left_insert_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_shift_left_insert_sisd (Sail.Int.toNatChecked (d)) datasize
    elements esize (Sail.Int.toNatChecked (n)) shift)


def decode_smax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) minimum (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_smin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) minimum (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_umax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) minimum (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_umin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) minimum (Sail.Int.toNatChecked (n))
    is_unsigned)


def decode_smaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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


end ArmFull.Functions
