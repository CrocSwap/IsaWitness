import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0015
import ArmFull.Fn.M0018
import ArmFull.Fn.M0019
import ArmFull.Fn.M0043
import ArmFull.Fn.M0044
import ArmFull.Fn.M0087
import ArmFull.Fn.M0099
import ArmFull.Fn.M0116
import ArmFull.Fn.M0145
import ArmFull.Fn.M0153
import ArmFull.Fn.M0154
import ArmFull.Fn.M0198
import ArmFull.Fn.M0583
import ArmFull.Fn.M0840

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

def UnallocatedA32_Instruction (instr : (BitVec 32)) : SailM Unit := do
  let nop ← (( do (undefined_bool_at (.site 7628) ()) ) : SailM Bool )
  let b__0 := instr
  let nop : Bool :=
    if (((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb b__0 27 16)) == (0x320#12 : (BitVec 12))) : Bool)
    then
      (let cond : (BitVec 4) := (Sail.BitVec.extractLsb instr 31 28)
      (cond != 0b1111#4))
    else
      (if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb b__0 31 24)) == (0xF4#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
               b__0 22 20)) == (0b001#3 : (BitVec 3)))) : Bool)
      then true
      else
        (if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb b__0 31 24)) == (0xF6#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                   b__0 22 20)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   b__0 4 4)) == (0#1 : (BitVec 1))))) : Bool)
        then true
        else false))
  let w__2 ← (( do
    if (((! nop) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do (AArch32_CurrentCond ()) ) : SailM (BitVec 4) )
        (ConditionHolds w__0))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (AArch32_UndefinedFault ()))
  else (pure (()))


def UnallocatedT32_32_Instruction (instr : (BitVec 32)) : SailM Unit := do
  let nop ← (( do (undefined_bool_at (← occLabel 7629) ()) ) : SailM Bool )
  let b__0 := instr
  let nop : Bool :=
    if ((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb b__0 31 20)) == (0xF3A#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               b__0 15 14)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                 b__0 12 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                 b__0 10 8)) == (0b000#3 : (BitVec 3)))))) : Bool)
    then true
    else
      (if ((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb b__0 31 20)) == (0xF93#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
               b__0 15 6)) == (0b1111000000#10 : (BitVec 10)))) : Bool)
      then true
      else
        (if ((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb b__0 31 20)) == (0xF93#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                 b__0 15 8)) == (0xFC#8 : (BitVec 8)))) : Bool)
        then true
        else
          (if ((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb b__0 31 20)) == (0xF9B#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                   b__0 15 12)) == (0xF#4 : (BitVec 4)))) : Bool)
          then true
          else
            (if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb b__0 31 24)) == (0xF9#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                     b__0 22 12)) == (0b01111111111#11 : (BitVec 11)))) : Bool)
            then true
            else false))))
  let nop := nop
  let w__2 ← (( do
    if ((! nop) : Bool)
    then
      (do
        let w__0 ← (( do (AArch32_CurrentCond ()) ) : SailM (BitVec 4) )
        (ConditionHolds w__0))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (AArch32_UndefinedFault ()))
  else (pure (()))


def UnallocatedT32_16_Instruction (instr : (BitVec 16)) : SailM Unit := do
  let nop ← (( do (undefined_bool_at (.site 7630) ()) ) : SailM Bool )
  let b__0 := instr
  let nop : Bool :=
    if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb b__0 15 8)) == (0xBF#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
             b__0 3 0)) == (0x0#4 : (BitVec 4)))) : Bool)
    then
      (let hint : (BitVec 4) := (Sail.BitVec.extractLsb instr 7 4)
      let b__1 := hint
      if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__1 3 1)) == (0b011#3 : (BitVec 3))) : Bool)
      then true
      else
        (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 3 3)) == (1#1 : (BitVec 1))) : Bool)
        then true
        else false))
    else false
  let w__2 ← (( do
    if (((! nop) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do (AArch32_CurrentCond ()) ) : SailM (BitVec 4) )
        (ConditionHolds w__0))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (AArch32_UndefinedFault ()))
  else (pure (()))


/-- Type quantifiers: size : Int -/
def HandleExternalReadAbort (memstatus : PhysMemRetStatus) (memaddrdesc : AddressDescriptor) (size : Int) (accdesc : AccessDescriptor) : SailM Unit := do
  let iswrite : Bool := false
  (HandleExternalAbort memstatus iswrite memaddrdesc size accdesc)


/-- Type quantifiers: size : Int -/
def HandleExternalWriteAbort (memstatus : PhysMemRetStatus) (memaddrdesc : AddressDescriptor) (size : Int) (accdesc : AccessDescriptor) : SailM Unit := do
  let iswrite : Bool := true
  (HandleExternalAbort memstatus iswrite memaddrdesc size accdesc)


/-- Type quantifiers: N : Nat, k_fpexc : Bool, k_isbfloat16 : Bool, List.elem N [16, 32, 64] -/
def FPRoundBase__1 (op : real) (fpcr : (BitVec 64)) (rounding : FPRounding) (isbfloat16 : Bool) (fpexc : Bool) (N : Nat) : SailM (BitVec N) := SailME.run do
  ArmFull.assert ((N == 16) || ((N == 32) || (N == 64))) "sail-arm/v8_base.sail:15647.38-15647.39"
  ArmFull.assert (bne op (0)) "sail-arm/v8_base.sail:15648.20-15648.21"
  ArmFull.assert (bne rounding FPRounding_TIEAWAY) "sail-arm/v8_base.sail:15649.41-15649.42"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 891)
      (Sail.Int.toNatChecked (N)))) ) : SailME (BitVec N) (BitVec N) )
  let minimum_exp ← (( do (undefined_int_at (← occLabel 892) ()) ) : SailME (BitVec N) Int )
  let F : Int := 7
  let E : Int := 5
  let (E, F, minimum_exp) : (Int × Int × Int) :=
    if ((N == 16) : Bool)
    then
      (let minimum_exp : Int := (Neg.neg 14)
      let E : Int := 5
      let F : Int := 10
      (E, F, minimum_exp))
    else
      (let (E, F, minimum_exp) : (Int × Int × Int) :=
        if (((N == 32) && isbfloat16) : Bool)
        then
          (let minimum_exp : Int := (Neg.neg 126)
          let E : Int := 8
          let F : Int := 7
          (E, F, minimum_exp))
        else
          (let (E, F, minimum_exp) : (Int × Int × Int) :=
            if ((N == 32) : Bool)
            then
              (let minimum_exp : Int := (Neg.neg 126)
              let E : Int := 8
              let F : Int := 23
              (E, F, minimum_exp))
            else
              (let minimum_exp : Int := (Neg.neg 1022)
              let E : Int := 11
              let F : Int := 52
              (E, F, minimum_exp))
          (E, F, minimum_exp))
      (E, F, minimum_exp))
  let minimum_exp : Int := minimum_exp
  let F : Int := F
  let E : Int := E
  let sign ← (( do (undefined_bitvector_at (← occLabel 893) 1) ) : SailME (BitVec N) (BitVec 1)
    )
  let mantissa ← (( do (undefined_real_at (← occLabel 894) ()) ) : SailME (BitVec N) real )
  let (mantissa, sign) : (real × (BitVec 1)) :=
    if ((lt_real op (0)) : Bool)
    then
      (let sign : (BitVec 1) := 1#1
      let mantissa : real := (neg_real op)
      (mantissa, sign))
    else
      (let sign : (BitVec 1) := 0#1
      let mantissa : real := op
      (mantissa, sign))
  let exponent : Int := 0
  let (exponent, mantissa) ← (( do
    let loop_vars ← sailWhileFuelM (fuel := 1048576) (fun (exponent, mantissa) => (pure (lt_real
        mantissa (1)))) (exponent, mantissa)
      fun (exponent, mantissa) => do
        (pure (let mantissa : real := (mult_real mantissa (2))
          let exponent : Int := (exponent -i 1)
          (exponent, mantissa) : (Int × real)))
    (pure loop_vars) ) : SailME (BitVec N) (Int × real) )
  let (exponent, mantissa) ← (( do
    let loop_vars_1 ← sailWhileFuelM (fuel := 1048576) (fun (exponent, mantissa) => (pure (gteq_real
        mantissa (2)))) (exponent, mantissa)
      fun (exponent, mantissa) => do
        (pure (let mantissa : real := (div_real mantissa (2))
          let exponent : Int := (exponent +i 1)
          (exponent, mantissa) : (Int × real)))
    (pure loop_vars_1) ) : SailME (BitVec N) (Int × real) )
  let exponent : Int := exponent
  let altfp ← (( do
    (pure ((← do
          if ((← do
               (HaveAltFP ())) : Bool)
          then
            (do
              let w__1 ← (( do (UsingAArch32 ()) ) : SailME (BitVec N) Bool )
              (pure (((! w__1) : Bool))))
          else (pure false)) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailME (BitVec N)
    Bool )
  if ((((! altfp) && ((((_get_FPCRType_FZ fpcr) == 1#1) && (N != 16)) || (((_get_FPCRType_FZ16 fpcr) == 1#1) && (N == 16)))) && (exponent <b minimum_exp)) : Bool)
  then
    (do
      let w__3 ← (( do (UsingAArch32 ()) ) : SailME (BitVec N) Bool )
      if (w__3 : Bool)
      then
        (do
          let w__4 ← (( do (FPSCR_read__1 ()) ) : SailME (BitVec N) (BitVec 32) )
          (FPSCR_write (_update_FPSCR_Type_UFC w__4 1#1)))
      else
        (do
          if (fpexc : Bool)
          then
            (do
              let w__5 ← (( do readReg FPSR ) : SailME (BitVec N) (BitVec 64) )
              writeReg FPSR (Sail.BitVec.updateSubrange w__5 3 3 1#1))
          else (pure (())))
      ((Sail.BitVec.castWidth ) <$> (FPZero sign N)))
  else
    (do
      let biased_exp_unconstrained : Int := ((exponent -i minimum_exp) +i 1)
      let int_mant_unconstrained : Int := (round_down (mult_real mantissa (real_power (2) F)))
      let error_unconstrained : real :=
        (sub_real (mult_real mantissa (real_power (2) F)) (to_real int_mant_unconstrained))
      let biased_exp : Int := (Max.max ((exponent -i minimum_exp) +i 1) 0)
      let mantissa : real :=
        if ((biased_exp == 0) : Bool)
        then (div_real mantissa (real_power (2) (minimum_exp -i exponent)))
        else mantissa
      let mantissa := mantissa
      let int_mant : Int := (round_down (mult_real mantissa (real_power (2) F)))
      let error : real := (sub_real (mult_real mantissa (real_power (2) F)) (to_real int_mant))
      let trapped_UF ← (( do
        if ((((_get_FPCRType_UFE fpcr) == 1#1) : Bool) : Bool)
        then
          (do
            if ((← do
                 let w__7 ← (( do (InStreamingMode ()) ) : SailME (BitVec N) Bool )
                 (pure (((! w__7) : Bool)))) : Bool)
            then (pure true)
            else
              (do
                (IsFullA64Enabled ())))
        else (pure false) ) : SailME (BitVec N) Bool )
      if ((((! altfp) && (biased_exp == 0)) && ((bne error (0)) || trapped_UF)) : Bool)
      then
        (do
          if (fpexc : Bool)
          then
            (do
              (FPProcessException FPExc_Underflow fpcr))
          else (pure (())))
      else (pure (()))
      let round_up_unconstrained ← (( do (undefined_bool_at (← occLabel 895) ()) ) : SailME
        (BitVec N) Bool )
      let round_up ← (( do (undefined_bool_at (← occLabel 896) ()) ) : SailME (BitVec N) Bool )
      let overflow_to_inf ← (( do (undefined_bool_at (← occLabel 897) ()) ) : SailME (BitVec N)
        Bool )
      let (overflow_to_inf, round_up) ← (( do
        if (altfp : Bool)
        then
          (do
            let (overflow_to_inf, round_up, round_up_unconstrained) : (Bool × Bool × Bool) :=
              match rounding with
              | .FPRounding_TIEEVEN =>
                (let round_up_unconstrained : Bool :=
                  ((gt_real error_unconstrained (1/2)) || ((eq_real error_unconstrained (1/2)) && ((BitVec.setWidth 1 (BitVec.join1 [(integer_access
                            int_mant_unconstrained 0)])) == 1#1)))
                let round_up : Bool :=
                  ((gt_real error (1/2)) || ((eq_real error (1/2)) && ((BitVec.setWidth 1 (BitVec.join1 [(integer_access
                            int_mant 0)])) == 1#1)))
                let overflow_to_inf : Bool := true
                (overflow_to_inf, round_up, round_up_unconstrained))
              | .FPRounding_POSINF =>
                (let round_up_unconstrained : Bool :=
                  ((bne error_unconstrained (0)) && (sign == 0#1))
                let round_up : Bool := ((bne error (0)) && (sign == 0#1))
                let overflow_to_inf : Bool := (sign == 0#1)
                (overflow_to_inf, round_up, round_up_unconstrained))
              | .FPRounding_NEGINF =>
                (let round_up_unconstrained : Bool :=
                  ((bne error_unconstrained (0)) && (sign == 1#1))
                let round_up : Bool := ((bne error (0)) && (sign == 1#1))
                let overflow_to_inf : Bool := (sign == 1#1)
                (overflow_to_inf, round_up, round_up_unconstrained))
              | .FPRounding_ZERO =>
                (let round_up_unconstrained : Bool := false
                let round_up : Bool := false
                let overflow_to_inf : Bool := false
                (overflow_to_inf, round_up, round_up_unconstrained))
              | .FPRounding_ODD =>
                (let round_up_unconstrained : Bool := false
                let round_up : Bool := false
                let overflow_to_inf : Bool := false
                (overflow_to_inf, round_up, round_up_unconstrained))
              | _ => (overflow_to_inf, round_up, round_up_unconstrained)
            let (biased_exp_unconstrained, int_mant_unconstrained) : (Int × Int) :=
              if (round_up_unconstrained : Bool)
              then
                (let int_mant_unconstrained : Int := (int_mant_unconstrained +i 1)
                let (biased_exp_unconstrained, int_mant_unconstrained) : (Int × Int) :=
                  if ((int_mant_unconstrained == (2 ^i (F +i 1))) : Bool)
                  then
                    (let biased_exp_unconstrained : Int := (biased_exp_unconstrained +i 1)
                    let int_mant_unconstrained : Int := (fdiv_int int_mant_unconstrained 2)
                    (biased_exp_unconstrained, int_mant_unconstrained))
                  else (biased_exp_unconstrained, int_mant_unconstrained)
                (biased_exp_unconstrained, int_mant_unconstrained))
              else (biased_exp_unconstrained, int_mant_unconstrained)
            let int_mant_unconstrained : Int := int_mant_unconstrained
            let biased_exp_unconstrained : Int := biased_exp_unconstrained
            if (((biased_exp_unconstrained <b 1) && (int_mant_unconstrained != 0)) : Bool)
            then
              (do
                if (((((_get_FPCRType_FZ fpcr) == 1#1) && (N != 16)) || (((_get_FPCRType_FZ16 fpcr) == 1#1) && (N == 16))) : Bool)
                then
                  (do
                    if (fpexc : Bool)
                    then
                      (do
                        let w__10 ← (( do readReg FPSR ) : SailME (BitVec N) (BitVec 64) )
                        writeReg FPSR (Sail.BitVec.updateSubrange w__10 3 3 1#1)
                        (FPProcessException FPExc_Inexact fpcr))
                    else (pure (()))
                    let w__11 ← (( do ((Sail.BitVec.castWidth ) <$> (FPZero sign N)) ) : SailME
                      (BitVec N) (BitVec N) )
                    SailME.throw (w__11 : (BitVec N)))
                else
                  (do
                    if (((bne error (0)) || trapped_UF) : Bool)
                    then
                      (do
                        if (fpexc : Bool)
                        then
                          (do
                            (FPProcessException FPExc_Underflow fpcr))
                        else (pure (())))
                    else (pure (()))))
            else (pure (()))
            (pure ((overflow_to_inf, round_up))))
        else
          (let (overflow_to_inf, round_up) : (Bool × Bool) :=
            match rounding with
            | .FPRounding_TIEEVEN =>
              (let round_up : Bool :=
                ((gt_real error (1/2)) || ((eq_real error (1/2)) && ((BitVec.setWidth 1 (BitVec.join1 [(integer_access
                          int_mant 0)])) == 1#1)))
              let overflow_to_inf : Bool := true
              (overflow_to_inf, round_up))
            | .FPRounding_POSINF =>
              (let round_up : Bool := ((bne error (0)) && (sign == 0#1))
              let overflow_to_inf : Bool := (sign == 0#1)
              (overflow_to_inf, round_up))
            | .FPRounding_NEGINF =>
              (let round_up : Bool := ((bne error (0)) && (sign == 1#1))
              let overflow_to_inf : Bool := (sign == 1#1)
              (overflow_to_inf, round_up))
            | .FPRounding_ZERO =>
              (let round_up : Bool := false
              let overflow_to_inf : Bool := false
              (overflow_to_inf, round_up))
            | .FPRounding_ODD =>
              (let round_up : Bool := false
              let overflow_to_inf : Bool := false
              (overflow_to_inf, round_up))
            | _ => (overflow_to_inf, round_up)
          (pure ((overflow_to_inf, round_up)))) ) : SailME (BitVec N) (Bool × Bool) )
      let (biased_exp, int_mant) : (Int × Int) :=
        if (round_up : Bool)
        then
          (let int_mant : Int := (int_mant +i 1)
          let biased_exp : Int :=
            if ((int_mant == (2 ^i F)) : Bool)
            then 1
            else biased_exp
          let (biased_exp, int_mant) : (Int × Int) :=
            if ((int_mant == (2 ^i (F +i 1))) : Bool)
            then
              (let biased_exp : Int := (biased_exp +i 1)
              let int_mant : Int := (fdiv_int int_mant 2)
              (biased_exp, int_mant))
            else (biased_exp, int_mant)
          (biased_exp, int_mant))
        else (biased_exp, int_mant)
      let biased_exp : Int := biased_exp
      let int_mant : Int :=
        if (((bne error (0)) && (BEq.beq rounding FPRounding_ODD)) : Bool)
        then (integer_update_subrange int_mant 0 0 1#1)
        else int_mant
      let int_mant : Int := int_mant
      let (error, result) ← (( do
        if (((N != 16) || ((_get_FPCRType_AHP fpcr) == 0#1)) : Bool)
        then
          (do
            if ((biased_exp ≥b ((2 ^i E) -i 1)) : Bool)
            then
              (do
                let w__14 ← (( do
                  if (overflow_to_inf : Bool)
                  then
                    (do
                      ((Sail.BitVec.castWidth ) <$> (FPInfinity sign N)))
                  else
                    (do
                      ((Sail.BitVec.castWidth ) <$> (FPMaxNormal sign N))) ) : SailME (BitVec N)
                  (BitVec N) )
                let result := (w__14 : (BitVec N))
                if (fpexc : Bool)
                then
                  (do
                    (FPProcessException FPExc_Overflow fpcr))
                else (pure (()))
                let error : real := (1)
                (pure ((error, result))))
            else
              (do
                ArmFull.assert ((N -i ((E +i F) +i 1)) ≥b 0) "sail-arm/v8_base.sail:15829.54-15829.55"
                let result : (BitVec N) :=
                  (Sail.BitVec.castWidth (((sign +++ (integer_subrange biased_exp (E -i 1) 0)) +++ (integer_subrange
                        int_mant (F -i 1) 0)) +++ (Zeros
                      (n := (Sail.Int.toNatChecked ((N -i ((E +i F) +i 1))))))))
                (pure ((error, result)))))
        else
          (do
            if ((biased_exp ≥b (2 ^i E)) : Bool)
            then
              (do
                let result : (BitVec N) :=
                  (Sail.BitVec.castWidth (sign +++ (Ones (n := (Sail.Int.toNatChecked ((N -i 1)))))))
                if (fpexc : Bool)
                then
                  (do
                    (FPProcessException FPExc_InvalidOp fpcr))
                else (pure (()))
                let error : real := (0)
                (pure ((error, result))))
            else
              (do
                ArmFull.assert ((N -i ((E +i F) +i 1)) ≥b 0) "sail-arm/v8_base.sail:15840.54-15840.55"
                let result : (BitVec N) :=
                  (Sail.BitVec.castWidth (((sign +++ (integer_subrange biased_exp (E -i 1) 0)) +++ (integer_subrange
                        int_mant (F -i 1) 0)) +++ (Zeros
                      (n := (Sail.Int.toNatChecked ((N -i ((E +i F) +i 1))))))))
                (pure ((error, result))))) ) : SailME (BitVec N) (real × (BitVec N)) )
      if ((bne error (0)) : Bool)
      then
        (do
          if (fpexc : Bool)
          then
            (do
              (FPProcessException FPExc_Inexact fpcr))
          else (pure (())))
      else (pure (()))
      (pure (result)))


/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, k_isbfloat16 : Bool, List.elem k_N [16, 32, 64] -/
def FPUnpackBase__1 (fpval : (BitVec k_N)) (fpcr_in : (BitVec 64)) (fpexc : Bool) (isbfloat16 : Bool) : SailM (FPType × (BitVec 1) × real) := do
  let exp16 ← (( do (undefined_bitvector_at (← occLabel 900) 5) ) : SailM (BitVec 5) )
  let exp64 ← (( do (undefined_bitvector_at (← occLabel 901) 11) ) : SailM (BitVec 11) )
  let frac16 ← (( do (undefined_bitvector_at (← occLabel 902) 10) ) : SailM (BitVec 10) )
  let frac64 ← (( do (undefined_bitvector_at (← occLabel 903) 52) ) : SailM (BitVec 52) )
  ArmFull.assert (((Sail.BitVec.length fpval) == 16) || (((Sail.BitVec.length fpval) == 32) || ((Sail.BitVec.length
          fpval) == 64))) "sail-arm/v8_base.sail:15949.41-15949.42"
  let fpcr : FPCRType := fpcr_in
  let altfp ← (( do
    if ((← do
         (HaveAltFP ())) : Bool)
    then
      (do
        let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  let fiz : Bool := (altfp && ((_get_FPCRType_FIZ fpcr) == 1#1))
  let fz : Bool :=
    (((_get_FPCRType_FZ fpcr) == 1#1) && (! (altfp && ((_get_FPCRType_AH fpcr) == 1#1))))
  let value_name ← (( do (undefined_real_at (← occLabel 904) ()) ) : SailM real )
  let sign ← (( do (undefined_bitvector_at (← occLabel 905) 1) ) : SailM (BitVec 1) )
  let fptype ← (( do (undefined_FPType (← occLabel 906) ()) ) : SailM FPType )
  let (fptype, sign, value_name) ← (( do
    if ((((Sail.BitVec.length fpval) == 16) && (! isbfloat16)) : Bool)
    then
      (let sign : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access fpval 15)]))
      let exp16 : (BitVec 5) := (Sail.BitVec.extractLsb fpval 14 10)
      let frac16 : (BitVec 10) := (Sail.BitVec.extractLsb fpval 9 0)
      let (fptype, value_name) : (FPType × real) :=
        if ((IsZero exp16) : Bool)
        then
          (let (fptype, value_name) : (FPType × real) :=
            if (((IsZero frac16) || ((_get_FPCRType_FZ16 fpcr) == 1#1)) : Bool)
            then
              (let fptype : FPType := FPType_Zero
              let value_name : real := (0)
              (fptype, value_name))
            else
              (let fptype : FPType := FPType_Denormal
              let value_name : real :=
                (mult_real (real_power (2) (Neg.neg 14))
                  (mult_real (to_real (BitVec.toNat frac16)) (real_power (2) (Neg.neg 10))))
              (fptype, value_name))
          (fptype, value_name))
        else
          (let (fptype, value_name) : (FPType × real) :=
            if (((IsOnes exp16) && ((_get_FPCRType_AHP fpcr) == 0#1)) : Bool)
            then
              (let (fptype, value_name) : (FPType × real) :=
                if ((IsZero frac16) : Bool)
                then
                  (let fptype : FPType := FPType_Infinity
                  let value_name : real := (real_power (2) 1000000)
                  (fptype, value_name))
                else
                  (let fptype : FPType :=
                    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access frac16 9)])) == 1#1) : Bool)
                    then FPType_QNaN
                    else FPType_SNaN
                  let value_name : real := (0)
                  (fptype, value_name))
              (fptype, value_name))
            else
              (let fptype : FPType := FPType_Nonzero
              let value_name : real :=
                (mult_real (real_power (2) ((BitVec.toNat exp16) -i 15))
                  (add_real (1)
                    (mult_real (to_real (BitVec.toNat frac16)) (real_power (2) (Neg.neg 10)))))
              (fptype, value_name))
          (fptype, value_name))
      (pure ((fptype, sign, value_name))))
    else
      (do
        if ((((Sail.BitVec.length fpval) == 32) || isbfloat16) : Bool)
        then
          (do
            let exp32 ← (( do (undefined_bitvector_at (← occLabel 907) 8) ) : SailM (BitVec 8) )
            let frac32 ← (( do (undefined_bitvector_at (← occLabel 908) 23) ) : SailM
              (BitVec 23) )
            let (exp32, frac32, sign) : ((BitVec 8) × (BitVec 23) × (BitVec 1)) :=
              if (isbfloat16 : Bool)
              then
                (let sign : (BitVec 1) :=
                  (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access fpval 15)]))
                let exp32 : (BitVec 8) := (Sail.BitVec.extractLsb fpval 14 7)
                let frac32 : (BitVec 23) :=
                  ((Sail.BitVec.extractLsb fpval 6 0) +++ (Zeros (n := 16)))
                (exp32, frac32, sign))
              else
                (let sign : (BitVec 1) :=
                  (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access fpval 31)]))
                let exp32 : (BitVec 8) := (Sail.BitVec.extractLsb fpval 30 23)
                let frac32 : (BitVec 23) := (Sail.BitVec.extractLsb fpval 22 0)
                (exp32, frac32, sign))
            let (fptype, value_name) ← (( do
              if ((IsZero exp32) : Bool)
              then
                (do
                  if ((IsZero frac32) : Bool)
                  then
                    (let fptype : FPType := FPType_Zero
                    let value_name : real := (0)
                    (pure ((fptype, value_name))))
                  else
                    (do
                      if ((fz || fiz) : Bool)
                      then
                        (do
                          let fptype : FPType := FPType_Zero
                          let value_name : real := (0)
                          if (fz : Bool)
                          then
                            (do
                              if (fpexc : Bool)
                              then
                                (do
                                  (FPProcessException FPExc_InputDenorm fpcr))
                              else (pure (())))
                          else (pure (()))
                          (pure ((fptype, value_name))))
                      else
                        (let fptype : FPType := FPType_Denormal
                        let value_name : real :=
                          (mult_real (real_power (2) (Neg.neg 126))
                            (mult_real (to_real (BitVec.toNat frac32)) (real_power (2) (Neg.neg 23))))
                        (pure ((fptype, value_name))))))
              else
                (let (fptype, value_name) : (FPType × real) :=
                  if ((IsOnes exp32) : Bool)
                  then
                    (let (fptype, value_name) : (FPType × real) :=
                      if ((IsZero frac32) : Bool)
                      then
                        (let fptype : FPType := FPType_Infinity
                        let value_name : real := (real_power (2) 1000000)
                        (fptype, value_name))
                      else
                        (let fptype : FPType :=
                          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access frac32 22)])) == 1#1) : Bool)
                          then FPType_QNaN
                          else FPType_SNaN
                        let value_name : real := (0)
                        (fptype, value_name))
                    (fptype, value_name))
                  else
                    (let fptype : FPType := FPType_Nonzero
                    let value_name : real :=
                      (mult_real (real_power (2) ((BitVec.toNat exp32) -i 127))
                        (add_real (1)
                          (mult_real (to_real (BitVec.toNat frac32)) (real_power (2) (Neg.neg 23)))))
                    (fptype, value_name))
                (pure ((fptype, value_name)))) ) : SailM (FPType × real) )
            (pure ((fptype, sign, value_name))))
        else
          (do
            let sign : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access fpval 63)]))
            let exp64 : (BitVec 11) := (Sail.BitVec.extractLsb fpval 62 52)
            let frac64 : (BitVec 52) := (Sail.BitVec.extractLsb fpval 51 0)
            let (fptype, value_name) ← (( do
              if ((IsZero exp64) : Bool)
              then
                (do
                  if ((IsZero frac64) : Bool)
                  then
                    (let fptype : FPType := FPType_Zero
                    let value_name : real := (0)
                    (pure ((fptype, value_name))))
                  else
                    (do
                      if ((fz || fiz) : Bool)
                      then
                        (do
                          let fptype : FPType := FPType_Zero
                          let value_name : real := (0)
                          if (fz : Bool)
                          then
                            (do
                              if (fpexc : Bool)
                              then
                                (do
                                  (FPProcessException FPExc_InputDenorm fpcr))
                              else (pure (())))
                          else (pure (()))
                          (pure ((fptype, value_name))))
                      else
                        (let fptype : FPType := FPType_Denormal
                        let value_name : real :=
                          (mult_real (real_power (2) (Neg.neg 1022))
                            (mult_real (to_real (BitVec.toNat frac64)) (real_power (2) (Neg.neg 52))))
                        (pure ((fptype, value_name))))))
              else
                (let (fptype, value_name) : (FPType × real) :=
                  if ((IsOnes exp64) : Bool)
                  then
                    (let (fptype, value_name) : (FPType × real) :=
                      if ((IsZero frac64) : Bool)
                      then
                        (let fptype : FPType := FPType_Infinity
                        let value_name : real := (real_power (2) 1000000)
                        (fptype, value_name))
                      else
                        (let fptype : FPType :=
                          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access frac64 51)])) == 1#1) : Bool)
                          then FPType_QNaN
                          else FPType_SNaN
                        let value_name : real := (0)
                        (fptype, value_name))
                    (fptype, value_name))
                  else
                    (let fptype : FPType := FPType_Nonzero
                    let value_name : real :=
                      (mult_real (real_power (2) ((BitVec.toNat exp64) -i 1023))
                        (add_real (1)
                          (mult_real (to_real (BitVec.toNat frac64)) (real_power (2) (Neg.neg 52)))))
                    (fptype, value_name))
                (pure ((fptype, value_name)))) ) : SailM (FPType × real) )
            (pure ((fptype, sign, value_name))))) ) : SailM (FPType × (BitVec 1) × real) )
  let value_name : real :=
    if ((sign == 1#1) : Bool)
    then (neg_real value_name)
    else value_name
  let value_name := value_name
  (pure ((fptype, sign, value_name)))


end ArmFull.Functions
