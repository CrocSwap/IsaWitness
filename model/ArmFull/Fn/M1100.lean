import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0018
import ArmFull.Fn.M0020
import ArmFull.Fn.M0049
import ArmFull.Fn.M0086
import ArmFull.Fn.M0116
import ArmFull.Fn.M0145
import ArmFull.Fn.M0178
import ArmFull.Fn.M0203
import ArmFull.Fn.M0215
import ArmFull.Fn.M0840
import ArmFull.Fn.M1071
import ArmFull.Fn.M1077
import ArmFull.Fn.M1078

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

def decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int := esize
  let elements : Nat := 1
  let comparison : CompareOp := CompareOp_LT
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (n)))


def decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_lessthan_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let comparison : CompareOp := CompareOp_LT
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


def decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let comparison : CompareOp := CompareOp_LT
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (n)))


def decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_lessthan_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
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
  let comparison : CompareOp := CompareOp_LT
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


def decode_fcmp_float_aarch64_instrs_float_compare_uncond (opc : (BitVec 2)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int := 16
  let datasize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure (16))
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let datasize : Int := datasize
  let signal_all_nans : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 1)])) == 1#1)
  let cmp_with_zero : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1)
  (execute_aarch64_instrs_float_compare_uncond cmp_with_zero (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) signal_all_nans)


def decode_fcmpe_float_aarch64_instrs_float_compare_uncond (opc : (BitVec 2)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int := 16
  let datasize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure (16))
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let datasize : Int := datasize
  let signal_all_nans : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 1)])) == 1#1)
  let cmp_with_zero : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc 0)])) == 1#1)
  (execute_aarch64_instrs_float_compare_uncond cmp_with_zero (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) signal_all_nans)


/-- Type quantifiers: d : Nat, dstsize : Nat, n : Nat, srcsize : Nat, List.elem srcsize [16, 32, 64]
  ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem dstsize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_convert_fp (d : Nat) (dstsize : Nat) (n : Nat) (srcsize : Nat) : SailM Unit := do
  (CheckFPEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n srcsize)) ) : SailM (BitVec srcsize)
    )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then
      (do
        (V_read d 128))
    else (pure ((Zeros (n := 128)))) ) : SailM (BitVec 128) )
  let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (FPConvert__1 operand fpcr dstsize)) ) : SailM
    (BitVec dstsize) )
  let w__2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_set result 0 dstsize (Sail.BitVec.castWidth w__1))) ) :
    SailM (BitVec 128) )
  let result := (w__2 : (BitVec 128))
  (V_set d 128 result)


def decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int := esize
  let elements : Nat := 1
  let rounding : FPRounding := FPRounding_TIEAWAY
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let rounding : FPRounding := FPRounding_TIEAWAY
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let rounding : FPRounding := FPRounding_TIEAWAY
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
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
  let rounding : FPRounding := FPRounding_TIEAWAY
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int := esize
  let elements : Nat := 1
  let rounding : FPRounding := FPRounding_TIEAWAY
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let rounding : FPRounding := FPRounding_TIEAWAY
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let rounding : FPRounding := FPRounding_TIEAWAY
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
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
  let rounding : FPRounding := FPRounding_TIEAWAY
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_fcvtas_float_aarch64_instrs_float_convert_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let intsize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Int := 16
  let op ← (( do (undefined_FPConvOp (← occLabel 4199) ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding (← occLabel 4200) ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool_at (← occLabel 4201) ()) ) : SailM Bool )
  let part : Int := 0
  let fltsize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 =>
      (do
        if (((Sail.BitVec.castWidth (m := 4) ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)) != 0b1101#4) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (128)))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure (16))
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let b__0 := ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)
  let (fltsize, is_unsigned, op, part, rounding) ← (( do
    if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b00#2 : (BitVec 2))) : Bool)
    then
      (do
        let w__0 ← (( do (FPDecodeRounding rmode) ) : SailM FPRounding )
        let rounding := (w__0 : FPRounding)
        let is_unsigned : Bool :=
          ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
        let op : FPConvOp := FPConvOp_CVT_FtoI
        (pure ((fltsize, is_unsigned, op, part, rounding))))
    else
      (do
        match b__0 with
        | 0b0100 =>
          (do
            let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__2 ← (( do (FPRoundingMode w__1) ) : SailM FPRounding )
            let rounding := (w__2 : FPRounding)
            let is_unsigned : Bool :=
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
            let op : FPConvOp := FPConvOp_CVT_ItoF
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1000 =>
          (let rounding : FPRounding := FPRounding_TIEAWAY
          let is_unsigned : Bool :=
            ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1100 =>
          (do
            if (((fltsize != 16) && ((fltsize != intsize) : Bool)) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            let op : FPConvOp :=
              if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1) : Bool)
              then FPConvOp_MOV_ItoF
              else FPConvOp_MOV_FtoI
            let part : Int := 0
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1101 =>
          (do
            if (((intsize != 64) || ((fltsize != 128) : Bool)) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            let op : FPConvOp :=
              if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1) : Bool)
              then FPConvOp_MOV_ItoF
              else FPConvOp_MOV_FtoI
            let part : Int := 1
            let fltsize : Int := 64
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1111 =>
          (do
            let w__3 ← (( do (HaveFJCVTZSExt ()) ) : SailM Bool )
            if ((! w__3) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            let rounding : FPRounding := FPRounding_ZERO
            let is_unsigned : Bool :=
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
            let op : FPConvOp := FPConvOp_CVT_FtoI_JS
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | _ => sailThrow ((Error_Undefined ()))) ) : SailM
    (Int × Bool × FPConvOp × Int × FPRounding) )
  let op := op
  let part : Int := part
  let fltsize : Int := fltsize
  match fltsize with
  | 16 =>
    (do
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 16
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 32 =>
    (do
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 32
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 64 =>
    (do
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 64
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 128 =>
    (do
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 128
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | _ =>
    (do
      ArmFull.assert false "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:14400.22-14400.23"
      throw Error.Exit)


def decode_fcvtau_float_aarch64_instrs_float_convert_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let intsize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Int := 16
  let op ← (( do (undefined_FPConvOp (← occLabel 4202) ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding (← occLabel 4203) ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool_at (← occLabel 4204) ()) ) : SailM Bool )
  let part : Int := 0
  let fltsize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 =>
      (do
        if (((Sail.BitVec.castWidth (m := 4) ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)) != 0b1101#4) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (128)))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure (16))
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let b__0 := ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)
  let (fltsize, is_unsigned, op, part, rounding) ← (( do
    if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b00#2 : (BitVec 2))) : Bool)
    then
      (do
        let w__0 ← (( do (FPDecodeRounding rmode) ) : SailM FPRounding )
        let rounding := (w__0 : FPRounding)
        let is_unsigned : Bool :=
          ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
        let op : FPConvOp := FPConvOp_CVT_FtoI
        (pure ((fltsize, is_unsigned, op, part, rounding))))
    else
      (do
        match b__0 with
        | 0b0100 =>
          (do
            let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__2 ← (( do (FPRoundingMode w__1) ) : SailM FPRounding )
            let rounding := (w__2 : FPRounding)
            let is_unsigned : Bool :=
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
            let op : FPConvOp := FPConvOp_CVT_ItoF
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1000 =>
          (let rounding : FPRounding := FPRounding_TIEAWAY
          let is_unsigned : Bool :=
            ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1100 =>
          (do
            if (((fltsize != 16) && ((fltsize != intsize) : Bool)) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            let op : FPConvOp :=
              if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1) : Bool)
              then FPConvOp_MOV_ItoF
              else FPConvOp_MOV_FtoI
            let part : Int := 0
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1101 =>
          (do
            if (((intsize != 64) || ((fltsize != 128) : Bool)) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            let op : FPConvOp :=
              if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1) : Bool)
              then FPConvOp_MOV_ItoF
              else FPConvOp_MOV_FtoI
            let part : Int := 1
            let fltsize : Int := 64
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1111 =>
          (do
            let w__3 ← (( do (HaveFJCVTZSExt ()) ) : SailM Bool )
            if ((! w__3) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            let rounding : FPRounding := FPRounding_ZERO
            let is_unsigned : Bool :=
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
            let op : FPConvOp := FPConvOp_CVT_FtoI_JS
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | _ => sailThrow ((Error_Undefined ()))) ) : SailM
    (Int × Bool × FPConvOp × Int × FPRounding) )
  let op := op
  let part : Int := part
  let fltsize : Int := fltsize
  match fltsize with
  | 16 =>
    (do
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 16
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 32 =>
    (do
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 32
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 64 =>
    (do
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 64
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 128 =>
    (do
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 128
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | _ =>
    (do
      ArmFull.assert false "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:14510.22-14510.23"
      throw Error.Exit)


def decode_fcvtms_float_aarch64_instrs_float_convert_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let intsize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Int := 16
  let op ← (( do (undefined_FPConvOp (← occLabel 4205) ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding (← occLabel 4206) ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool_at (← occLabel 4207) ()) ) : SailM Bool )
  let part : Int := 0
  let fltsize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 =>
      (do
        if (((Sail.BitVec.castWidth (m := 4) ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)) != 0b1101#4) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (128)))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure (16))
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let b__0 := ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)
  let (fltsize, is_unsigned, op, part, rounding) ← (( do
    if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b00#2 : (BitVec 2))) : Bool)
    then
      (do
        let w__0 ← (( do (FPDecodeRounding rmode) ) : SailM FPRounding )
        let rounding := (w__0 : FPRounding)
        let is_unsigned : Bool :=
          ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
        let op : FPConvOp := FPConvOp_CVT_FtoI
        (pure ((fltsize, is_unsigned, op, part, rounding))))
    else
      (do
        match b__0 with
        | 0b0100 =>
          (do
            let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
            let w__2 ← (( do (FPRoundingMode w__1) ) : SailM FPRounding )
            let rounding := (w__2 : FPRounding)
            let is_unsigned : Bool :=
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
            let op : FPConvOp := FPConvOp_CVT_ItoF
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1000 =>
          (let rounding : FPRounding := FPRounding_TIEAWAY
          let is_unsigned : Bool :=
            ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1100 =>
          (do
            if (((fltsize != 16) && ((fltsize != intsize) : Bool)) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            let op : FPConvOp :=
              if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1) : Bool)
              then FPConvOp_MOV_ItoF
              else FPConvOp_MOV_FtoI
            let part : Int := 0
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1101 =>
          (do
            if (((intsize != 64) || ((fltsize != 128) : Bool)) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            let op : FPConvOp :=
              if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1) : Bool)
              then FPConvOp_MOV_ItoF
              else FPConvOp_MOV_FtoI
            let part : Int := 1
            let fltsize : Int := 64
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | 0b1111 =>
          (do
            let w__3 ← (( do (HaveFJCVTZSExt ()) ) : SailM Bool )
            if ((! w__3) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            let rounding : FPRounding := FPRounding_ZERO
            let is_unsigned : Bool :=
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
            let op : FPConvOp := FPConvOp_CVT_FtoI_JS
            (pure ((fltsize, is_unsigned, op, part, rounding))))
        | _ => sailThrow ((Error_Undefined ()))) ) : SailM
    (Int × Bool × FPConvOp × Int × FPRounding) )
  let op := op
  let part : Int := part
  let fltsize : Int := fltsize
  match fltsize with
  | 16 =>
    (do
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 16
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 32 =>
    (do
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 32
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 64 =>
    (do
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 64
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | 128 =>
    (do
      (execute_aarch64_instrs_float_convert_int (Sail.Int.toNatChecked (d)) 128
        (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op
        (Sail.Int.toNatChecked (part)) rounding is_unsigned))
  | _ =>
    (do
      ArmFull.assert false "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:14620.22-14620.23"
      throw Error.Exit)


end ArmFull.Functions
