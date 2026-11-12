import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0020
import ArmFull.Fn.M0086
import ArmFull.Fn.M0145
import ArmFull.Fn.M1097
import ArmFull.Fn.M1098
import ArmFull.Fn.M1099
import ArmFull.Fn.M1100
import ArmFull.Fn.M1103
import ArmFull.Fn.M1104

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

def decode_fneg_float_aarch64_instrs_float_arithmetic_unary (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (ftype : (BitVec 2)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
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
  let fpop ← (( do (undefined_FPUnaryOp (← occLabel 4109) ()) ) : SailM FPUnaryOp )
  let fpop : FPUnaryOp :=
    match opc with
    | 0b00 => FPUnaryOp_MOV
    | 0b01 => FPUnaryOp_ABS
    | 0b10 => FPUnaryOp_NEG
    | _ => FPUnaryOp_SQRT
  let fpop := fpop
  (execute_aarch64_instrs_float_arithmetic_unary (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) fpop (Sail.Int.toNatChecked (n)))


def decode_fsqrt_float_aarch64_instrs_float_arithmetic_unary (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (ftype : (BitVec 2)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
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
  let fpop ← (( do (undefined_FPUnaryOp (← occLabel 4110) ()) ) : SailM FPUnaryOp )
  let fpop : FPUnaryOp :=
    match opc with
    | 0b00 => FPUnaryOp_MOV
    | 0b01 => FPUnaryOp_ABS
    | 0b10 => FPUnaryOp_NEG
    | _ => FPUnaryOp_SQRT
  let fpop := fpop
  (execute_aarch64_instrs_float_arithmetic_unary (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) fpop (Sail.Int.toNatChecked (n)))


def decode_fadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements esize (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) pair)


def decode_fadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) pair)


def decode_faddp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements esize (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) pair)


def decode_faddp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) pair)


def decode_fadd_float_aarch64_instrs_float_arithmetic_add_sub (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
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
  let sub_op : Bool := (op == 1#1)
  (execute_aarch64_instrs_float_arithmetic_add_sub (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op)


def decode_fsub_float_aarch64_instrs_float_arithmetic_add_sub (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
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
  let sub_op : Bool := (op == 1#1)
  (execute_aarch64_instrs_float_arithmetic_add_sub (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op)


def decode_fcadd_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp_complex (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rot : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFCADDExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 0#1) && (size == 0b11#2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  if (((! (HaveFP16Ext ())) && (esize == 16)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp_complex
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) rot)


def decode_fcmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_complex (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rot : (BitVec 2)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFCADDExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 0#1) && (size == 0b11#2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  if (((! (HaveFP16Ext ())) && (esize == 16)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_complex
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) rot)


def decode_fcmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_complex (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (rot : (BitVec 2)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveFCADDExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat (M +++ Rm))
  let index ← (( do (undefined_int_at (← occLabel 4191) ()) ) : SailM Int )
  if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let index : Int :=
    if ((size == 0b01#2) : Bool)
    then (BitVec.toNat (H +++ L))
    else index
  let index : Int :=
    if ((size == 0b10#2) : Bool)
    then (BitVec.toNat H)
    else index
  let index : Int := index
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  if (((! (HaveFP16Ext ())) && (esize == 16)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  if (((size == 0b10#2) && ((L == 1#1) || (Q == 0#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((((size == 0b01#2) && (H == 1#1)) && (Q == 0#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  ArmFull.assert ((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) "sail-arm/instrs64.sail:13687.45-13687.46"
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_complex
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) rot)


def decode_fcvt_float_aarch64_instrs_float_convert_fp (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (ftype : (BitVec 2)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let srcsize : Int := 16
  let dstsize : Int := 16
  if ((ftype == opc) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let srcsize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ => (pure (16)) ) : SailM Int )
  let srcsize : Int := srcsize
  let dstsize ← (( do
    match opc with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ => (pure (16)) ) : SailM Int )
  let dstsize : Int := dstsize
  (execute_aarch64_instrs_float_convert_fp (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (dstsize)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (srcsize)))


def decode_fcvtl_advsimd_aarch64_instrs_vector_arithmetic_unary_float_widen (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 16 (BitVec.toNat sz))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (fdiv_int datasize esize)
  ArmFull.assert ((esize == 16) || (esize == 32)) "sail-arm/instrs64.sail:15869.41-15869.42"
  (execute_aarch64_instrs_vector_arithmetic_unary_float_widen (Sail.Int.toNatChecked (d)) datasize
    elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (part)))


def decode_fcvtn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_narrow (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 16 (BitVec.toNat sz))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (fdiv_int datasize esize)
  ArmFull.assert ((esize == 16) || (esize == 32)) "sail-arm/instrs64.sail:16763.41-16763.42"
  (execute_aarch64_instrs_vector_arithmetic_unary_float_narrow (Sail.Int.toNatChecked (d)) datasize
    elements (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (part)))


def decode_fdiv_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_div_fp16 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_div_fp16 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements esize (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)))


def decode_fdiv_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_div (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_div_fp16 (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_fdiv_float_aarch64_instrs_float_arithmetic_div (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
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
  (execute_aarch64_instrs_float_arithmetic_div (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_fmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (o1 : (BitVec 1)) (ftype : (BitVec 2)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let a : Int := (BitVec.toNat Ra)
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
  let opa_neg : Bool := (o1 == 1#1)
  let op1_neg : Bool := (o0 != o1)
  (execute_aarch64_instrs_float_arithmetic_mul_add_sub (Sail.Int.toNatChecked (a))
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) op1_neg opa_neg)


def decode_fmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (o1 : (BitVec 1)) (ftype : (BitVec 2)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let a : Int := (BitVec.toNat Ra)
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
  let opa_neg : Bool := (o1 == 1#1)
  let op1_neg : Bool := (o0 != o1)
  (execute_aarch64_instrs_float_arithmetic_mul_add_sub (Sail.Int.toNatChecked (a))
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) op1_neg opa_neg)


def decode_fnmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (o1 : (BitVec 1)) (ftype : (BitVec 2)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let a : Int := (BitVec.toNat Ra)
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
  let opa_neg : Bool := (o1 == 1#1)
  let op1_neg : Bool := (o0 != o1)
  (execute_aarch64_instrs_float_arithmetic_mul_add_sub (Sail.Int.toNatChecked (a))
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) op1_neg opa_neg)


def decode_fnmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (o1 : (BitVec 1)) (ftype : (BitVec 2)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let a : Int := (BitVec.toNat Ra)
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
  let opa_neg : Bool := (o1 == 1#1)
  let op1_neg : Bool := (o0 != o1)
  (execute_aarch64_instrs_float_arithmetic_mul_add_sub (Sail.Int.toNatChecked (a))
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) op1_neg opa_neg)


def decode_fmax_float_aarch64_instrs_float_arithmetic_max_min (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
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
  let operation ← (( do (undefined_FPMaxMinOp (← occLabel 4262) ()) ) : SailM FPMaxMinOp )
  let operation : FPMaxMinOp :=
    match op with
    | 0b00 => FPMaxMinOp_MAX
    | 0b01 => FPMaxMinOp_MIN
    | 0b10 => FPMaxMinOp_MAXNUM
    | _ => FPMaxMinOp_MINNUM
  let operation := operation
  (execute_aarch64_instrs_float_arithmetic_max_min (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    operation)


def decode_fmaxnm_float_aarch64_instrs_float_arithmetic_max_min (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
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
  let operation ← (( do (undefined_FPMaxMinOp (← occLabel 4263) ()) ) : SailM FPMaxMinOp )
  let operation : FPMaxMinOp :=
    match op with
    | 0b00 => FPMaxMinOp_MAX
    | 0b01 => FPMaxMinOp_MIN
    | 0b10 => FPMaxMinOp_MAXNUM
    | _ => FPMaxMinOp_MINNUM
  let operation := operation
  (execute_aarch64_instrs_float_arithmetic_max_min (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    operation)


def decode_fmin_float_aarch64_instrs_float_arithmetic_max_min (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
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
  let operation ← (( do (undefined_FPMaxMinOp (← occLabel 4264) ()) ) : SailM FPMaxMinOp )
  let operation : FPMaxMinOp :=
    match op with
    | 0b00 => FPMaxMinOp_MAX
    | 0b01 => FPMaxMinOp_MIN
    | 0b10 => FPMaxMinOp_MAXNUM
    | _ => FPMaxMinOp_MINNUM
  let operation := operation
  (execute_aarch64_instrs_float_arithmetic_max_min (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    operation)


def decode_fminnm_float_aarch64_instrs_float_arithmetic_max_min (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
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
  let operation ← (( do (undefined_FPMaxMinOp (← occLabel 4265) ()) ) : SailM FPMaxMinOp )
  let operation : FPMaxMinOp :=
    match op with
    | 0b00 => FPMaxMinOp_MAX
    | 0b01 => FPMaxMinOp_MIN
    | 0b10 => FPMaxMinOp_MAXNUM
    | _ => FPMaxMinOp_MINNUM
  let operation := operation
  (execute_aarch64_instrs_float_arithmetic_max_min (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    operation)


def decode_fmax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (o1 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (m)) minimum (Sail.Int.toNatChecked (n)) pair)


def decode_fmax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) minimum (Sail.Int.toNatChecked (n))
    pair)


end ArmFull.Functions
