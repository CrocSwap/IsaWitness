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
import ArmFull.Fn.M0227
import ArmFull.Fn.M0840
import ArmFull.Fn.M0852
import ArmFull.Fn.M1041
import ArmFull.Fn.M1071
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

def decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := esize
  let elements : Nat := 1
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements esize
    (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)) rounding is_unsigned)


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, part : Nat, List.elem
  part [0, 1] ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_float_narrow (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do
    ((Sail.BitVec.castWidth ) <$> (V_read n (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM
    (BitVec (2 * datasize)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4243)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
              (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (FPConvert__1 w__0 w__1 esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec datasize) )
  (Vpart_set d part datasize (Sail.BitVec.castWidth result))


def decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((sz == 0#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let datasize : Int := esize
  let elements : Nat := 1
  let part : Nat := 0
  (execute_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements esize (Sail.Int.toNatChecked (n)) part)


def decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((sz == 0#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let datasize : Nat := 64
  let elements : Nat := 2
  let part : Int := (BitVec.toNat Q)
  (execute_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd (Sail.Int.toNatChecked (d))
    datasize elements esize (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)))


def decode_fcvtzs_float_fix_aarch64_instrs_float_convert_fix (Rd : (BitVec 5)) (Rn : (BitVec 5)) (scale : (BitVec 6)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let intsize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Int := 16
  let op ← (( do (undefined_FPConvOp (← occLabel 4246) ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding (← occLabel 4247) ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool_at (← occLabel 4248) ()) ) : SailM Bool )
  let fltsize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure (16))
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let fltsize : Int := fltsize
  if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access scale 5)])) == 0#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let fracbits : Int := (64 -i (BitVec.toNat scale))
  let (is_unsigned, op, rounding) ← (( do
    match (BitVec.setWidth 4 ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)) with
    | 0b0011 =>
      (let rounding : FPRounding := FPRounding_ZERO
      let is_unsigned : Bool :=
        ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
      let op : FPConvOp := FPConvOp_CVT_FtoI
      (pure ((is_unsigned, op, rounding))))
    | 0b0100 =>
      (do
        let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
        let w__1 ← (( do (FPRoundingMode w__0) ) : SailM FPRounding )
        let rounding := (w__1 : FPRounding)
        let is_unsigned : Bool :=
          ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
        let op : FPConvOp := FPConvOp_CVT_ItoF
        (pure ((is_unsigned, op, rounding))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × FPConvOp × FPRounding) )
  (execute_aarch64_instrs_float_convert_fix (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (fltsize)) (Sail.Int.toNatChecked (fracbits))
    (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op rounding is_unsigned)


def decode_fcvtzu_float_fix_aarch64_instrs_float_convert_fix (Rd : (BitVec 5)) (Rn : (BitVec 5)) (scale : (BitVec 6)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let intsize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Int := 16
  let op ← (( do (undefined_FPConvOp (← occLabel 4249) ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding (← occLabel 4250) ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool_at (← occLabel 4251) ()) ) : SailM Bool )
  let fltsize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure (16))
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let fltsize : Int := fltsize
  if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access scale 5)])) == 0#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let fracbits : Int := (64 -i (BitVec.toNat scale))
  let (is_unsigned, op, rounding) ← (( do
    match (BitVec.setWidth 4 ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)) with
    | 0b0011 =>
      (let rounding : FPRounding := FPRounding_ZERO
      let is_unsigned : Bool :=
        ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
      let op : FPConvOp := FPConvOp_CVT_FtoI
      (pure ((is_unsigned, op, rounding))))
    | 0b0100 =>
      (do
        let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
        let w__1 ← (( do (FPRoundingMode w__0) ) : SailM FPRounding )
        let rounding := (w__1 : FPRounding)
        let is_unsigned : Bool :=
          ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
        let op : FPConvOp := FPConvOp_CVT_ItoF
        (pure ((is_unsigned, op, rounding))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × FPConvOp × FPRounding) )
  (execute_aarch64_instrs_float_convert_fix (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (fltsize)) (Sail.Int.toNatChecked (fracbits))
    (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op rounding is_unsigned)


def decode_scvtf_float_fix_aarch64_instrs_float_convert_fix (Rd : (BitVec 5)) (Rn : (BitVec 5)) (scale : (BitVec 6)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let intsize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Int := 16
  let op ← (( do (undefined_FPConvOp (← occLabel 4252) ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding (← occLabel 4253) ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool_at (← occLabel 4254) ()) ) : SailM Bool )
  let fltsize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure (16))
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let fltsize : Int := fltsize
  if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access scale 5)])) == 0#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let fracbits : Int := (64 -i (BitVec.toNat scale))
  let (is_unsigned, op, rounding) ← (( do
    match (BitVec.setWidth 4 ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)) with
    | 0b0011 =>
      (let rounding : FPRounding := FPRounding_ZERO
      let is_unsigned : Bool :=
        ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
      let op : FPConvOp := FPConvOp_CVT_FtoI
      (pure ((is_unsigned, op, rounding))))
    | 0b0100 =>
      (do
        let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
        let w__1 ← (( do (FPRoundingMode w__0) ) : SailM FPRounding )
        let rounding := (w__1 : FPRounding)
        let is_unsigned : Bool :=
          ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
        let op : FPConvOp := FPConvOp_CVT_ItoF
        (pure ((is_unsigned, op, rounding))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × FPConvOp × FPRounding) )
  (execute_aarch64_instrs_float_convert_fix (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (fltsize)) (Sail.Int.toNatChecked (fracbits))
    (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op rounding is_unsigned)


def decode_ucvtf_float_fix_aarch64_instrs_float_convert_fix (Rd : (BitVec 5)) (Rn : (BitVec 5)) (scale : (BitVec 6)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let intsize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Int := 16
  let op ← (( do (undefined_FPConvOp (← occLabel 4255) ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding (← occLabel 4256) ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool_at (← occLabel 4257) ()) ) : SailM Bool )
  let fltsize ← (( do
    match ftype with
    | 0b00 => (pure (32))
    | 0b01 => (pure (64))
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure (16))
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let fltsize : Int := fltsize
  if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access scale 5)])) == 0#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let fracbits : Int := (64 -i (BitVec.toNat scale))
  let (is_unsigned, op, rounding) ← (( do
    match (BitVec.setWidth 4 ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)) with
    | 0b0011 =>
      (let rounding : FPRounding := FPRounding_ZERO
      let is_unsigned : Bool :=
        ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
      let op : FPConvOp := FPConvOp_CVT_FtoI
      (pure ((is_unsigned, op, rounding))))
    | 0b0100 =>
      (do
        let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
        let w__1 ← (( do (FPRoundingMode w__0) ) : SailM FPRounding )
        let rounding := (w__1 : FPRounding)
        let is_unsigned : Bool :=
          ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opcode 0)])) == 1#1)
        let op : FPConvOp := FPConvOp_CVT_ItoF
        (pure ((is_unsigned, op, rounding))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × FPConvOp × FPRounding) )
  (execute_aarch64_instrs_float_convert_fix (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (fltsize)) (Sail.Int.toNatChecked (fracbits))
    (Sail.Int.toNatChecked (intsize)) (Sail.Int.toNatChecked (n)) op rounding is_unsigned)


def decode_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((let b__0 := immh
       (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b000#3 : (BitVec 3))) : Bool)
       then true
       else false : Bool)) || ((let b__1 := immh
         (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__1 3 1)) == (0b001#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool)) && (! (HaveFP16Ext ())))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int :=
    if ((let b__3 := immh
       (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__3 3 3)) == (1#1 : (BitVec 1))) : Bool)
       then true
       else false : Bool)) : Bool)
    then 64
    else
      (if ((let b__2 := immh
         (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__2 3 2)) == (0b01#2 : (BitVec 2))) : Bool)
         then true
         else false : Bool)) : Bool)
      then 32
      else 16)
  let datasize : Int := esize
  let elements : Nat := 1
  let fracbits : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let rounding : FPRounding := FPRounding_ZERO
  (execute_aarch64_instrs_vector_shift_conv_float_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize)) fracbits
    (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then sailThrow ((Error_See "asimdimm"))
  else (pure (()))
  if (((let b__0 := immh
       (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b000#3 : (BitVec 3))) : Bool)
       then true
       else false : Bool)) || ((let b__1 := immh
         (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__1 3 1)) == (0b001#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool)) && (! (HaveFP16Ext ())))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int :=
    if ((let b__3 := immh
       (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__3 3 3)) == (1#1 : (BitVec 1))) : Bool)
       then true
       else false : Bool)) : Bool)
    then 64
    else
      (if ((let b__2 := immh
         (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__2 3 2)) == (0b01#2 : (BitVec 2))) : Bool)
         then true
         else false : Bool)) : Bool)
      then 32
      else 16)
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let fracbits : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let rounding : FPRounding := FPRounding_ZERO
  (execute_aarch64_instrs_vector_shift_conv_float_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize)) fracbits
    (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((let b__0 := immh
       (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b000#3 : (BitVec 3))) : Bool)
       then true
       else false : Bool)) || ((let b__1 := immh
         (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__1 3 1)) == (0b001#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool)) && (! (HaveFP16Ext ())))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int :=
    if ((let b__3 := immh
       (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__3 3 3)) == (1#1 : (BitVec 1))) : Bool)
       then true
       else false : Bool)) : Bool)
    then 64
    else
      (if ((let b__2 := immh
         (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__2 3 2)) == (0b01#2 : (BitVec 2))) : Bool)
         then true
         else false : Bool)) : Bool)
      then 32
      else 16)
  let datasize : Int := esize
  let elements : Nat := 1
  let fracbits : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let rounding : FPRounding := FPRounding_ZERO
  (execute_aarch64_instrs_vector_shift_conv_float_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize)) fracbits
    (Sail.Int.toNatChecked (n)) rounding is_unsigned)


def decode_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then sailThrow ((Error_See "asimdimm"))
  else (pure (()))
  if (((let b__0 := immh
       (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b000#3 : (BitVec 3))) : Bool)
       then true
       else false : Bool)) || ((let b__1 := immh
         (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__1 3 1)) == (0b001#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool)) && (! (HaveFP16Ext ())))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immh 3)])) +++ Q) == 0b10#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int :=
    if ((let b__3 := immh
       (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__3 3 3)) == (1#1 : (BitVec 1))) : Bool)
       then true
       else false : Bool)) : Bool)
    then 64
    else
      (if ((let b__2 := immh
         (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__2 3 2)) == (0b01#2 : (BitVec 2))) : Bool)
         then true
         else false : Bool)) : Bool)
      then 32
      else 16)
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let fracbits : Int := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let rounding : FPRounding := FPRounding_ZERO
  (execute_aarch64_instrs_vector_shift_conv_float_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize)) fracbits
    (Sail.Int.toNatChecked (n)) rounding is_unsigned)


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤
  n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_div_fp16 (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4259)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4260)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4261)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 := (w__0 : (BitVec esize))
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 := (w__1 : (BitVec esize))
          let w__2 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (FPDiv element1 element2 w__2) ) : SailM (BitVec esize) )
          let w__4 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__3)) ) : SailM
            (BitVec datasize) )
          let result := (w__4 : (BitVec datasize))
          (pure ((element1, element2, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_arithmetic_div (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n esize)) ) : SailM (BitVec esize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m esize)) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then
      (do
        (V_read n 128))
    else (pure ((Zeros (n := 128)))) ) : SailM (BitVec 128) )
  let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
  let w__2 ← (( do (FPDiv operand1 operand2 w__1) ) : SailM (BitVec esize) )
  let w__3 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_set result 0 esize (Sail.BitVec.castWidth w__2))) ) : SailM
    (BitVec 128) )
  let result := (w__3 : (BitVec 128))
  (V_set d 128 result)


/-- Type quantifiers: a : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_opa_neg :
  Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 -/
def execute_aarch64_instrs_float_arithmetic_mul_add_sub (a : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (opa_neg : Bool) : SailM Unit := do
  (CheckFPEnabled64 ())
  let operanda ← (( do ((Sail.BitVec.castWidth ) <$> (V_read a esize)) ) : SailM (BitVec esize) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n esize)) ) : SailM (BitVec esize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m esize)) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then
      (do
        (V_read a 128))
    else (pure ((Zeros (n := 128)))) ) : SailM (BitVec 128) )
  let operanda ← (( do
    if (opa_neg : Bool)
    then
      (do
        (FPNeg operanda))
    else (pure (operanda)) ) : SailM (BitVec esize) )
  let operand1 ← (( do
    if (op1_neg : Bool)
    then
      (do
        (FPNeg operand1))
    else (pure (operand1)) ) : SailM (BitVec esize) )
  let w__3 ← (( do (FPMulAdd operanda operand1 operand2 fpcr) ) : SailM (BitVec esize) )
  let w__4 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_set result 0 esize (Sail.BitVec.castWidth w__3))) ) : SailM
    (BitVec 128) )
  let result := (w__4 : (BitVec 128))
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_arithmetic_max_min (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (operation : FPMaxMinOp) : SailM Unit := do
  (CheckFPEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n esize)) ) : SailM (BitVec esize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m esize)) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then
      (do
        (V_read n 128))
    else (pure ((Zeros (n := 128)))) ) : SailM (BitVec 128) )
  let result ← (( do
    match operation with
    | .FPMaxMinOp_MAX =>
      (do
        let w__1 ← (( do (FPMax operand1 operand2 fpcr) ) : SailM (BitVec esize) )
        ((Sail.BitVec.castWidth ) <$> (Elem_set result 0 esize (Sail.BitVec.castWidth w__1))))
    | .FPMaxMinOp_MIN =>
      (do
        let w__3 ← (( do (FPMin operand1 operand2 fpcr) ) : SailM (BitVec esize) )
        ((Sail.BitVec.castWidth ) <$> (Elem_set result 0 esize (Sail.BitVec.castWidth w__3))))
    | .FPMaxMinOp_MAXNUM =>
      (do
        let w__5 ← (( do (FPMaxNum operand1 operand2 fpcr) ) : SailM (BitVec esize) )
        ((Sail.BitVec.castWidth ) <$> (Elem_set result 0 esize (Sail.BitVec.castWidth w__5))))
    | .FPMaxMinOp_MINNUM =>
      (do
        let w__7 ← (( do (FPMinNum operand1 operand2 fpcr) ) : SailM (BitVec esize) )
        ((Sail.BitVec.castWidth ) <$> (Elem_set result 0 esize (Sail.BitVec.castWidth w__7)))) ) :
    SailM (BitVec 128) )
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, k_minimum :
  Bool, n : Nat, k_pair : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (minimum : Bool) (n : Nat) (pair : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4266)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let concat : (BitVec (2 * datasize)) := (Sail.BitVec.castWidth (operand2 +++ operand1))
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4267)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4268)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result) := loop_vars
        loop_vars ← do
          let (element1, element2) ← (( do
            if (pair : Bool)
            then
              (do
                let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read concat (2 *i e) esize))
                  ) : SailM (BitVec esize) )
                let element1 := (w__0 : (BitVec esize))
                let w__1 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read concat ((2 *i e) +i 1) esize)) ) : SailM
                  (BitVec esize) )
                let element2 := (w__1 : (BitVec esize))
                (pure ((element1, element2))))
            else
              (do
                let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                  SailM (BitVec esize) )
                let element1 := (w__2 : (BitVec esize))
                let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
                  SailM (BitVec esize) )
                let element2 := (w__3 : (BitVec esize))
                (pure ((element1, element2)))) ) : SailM ((BitVec esize) × (BitVec esize)) )
          let result ← (( do
            if (minimum : Bool)
            then
              (do
                let w__4 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__5 ← (( do (FPMin element1 element2 w__4) ) : SailM (BitVec esize) )
                (Elem_set result e esize (Sail.BitVec.castWidth w__5)))
            else
              (do
                let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__8 ← (( do (FPMax element1 element2 w__7) ) : SailM (BitVec esize) )
                (Elem_set result e esize (Sail.BitVec.castWidth w__8))) ) : SailM (BitVec datasize)
            )
          (pure ((element1, element2, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


end ArmFull.Functions
