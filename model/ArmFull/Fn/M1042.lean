import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0015
import ArmFull.Fn.M0017
import ArmFull.Fn.M0018
import ArmFull.Fn.M0034
import ArmFull.Fn.M0048
import ArmFull.Fn.M0050
import ArmFull.Fn.M0087
import ArmFull.Fn.M0097
import ArmFull.Fn.M0116
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0153
import ArmFull.Fn.M0154
import ArmFull.Fn.M0155
import ArmFull.Fn.M0166
import ArmFull.Fn.M0167
import ArmFull.Fn.M0168
import ArmFull.Fn.M0173
import ArmFull.Fn.M0217
import ArmFull.Fn.M0218
import ArmFull.Fn.M0244
import ArmFull.Fn.M0255
import ArmFull.Fn.M0257
import ArmFull.Fn.M0840
import ArmFull.Fn.M0851
import ArmFull.Fn.M0852
import ArmFull.Fn.M0923
import ArmFull.Fn.M1002

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

/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPRSqrtEstimate (operand : (BitVec k_N)) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  let estimate ← (( do (undefined_int_at (← occLabel 1115) ()) ) : SailM Int )
  let fptype ← (( do (undefined_FPType (← occLabel 1116) ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector_at (← occLabel 1117) 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real_at (← occLabel 1118) ()) ) : SailM real )
  ArmFull.assert (((Sail.BitVec.length operand) == 16) || (((Sail.BitVec.length operand) == 32) || ((Sail.BitVec.length
          operand) == 64))) "sail-arm/v8_base.sail:17615.41-17615.42"
  let fpcr : FPCRType := fpcr_in
  let altfp ← (( do
    (pure ((← do
          if ((← do
               (HaveAltFP ())) : Bool)
          then
            (do
              let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              (pure (((! w__1) : Bool))))
          else (pure false)) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  let fpexc : Bool := (! altfp)
  let fpcr : (BitVec 64) :=
    if (altfp : Bool)
    then
      (let fpcr : FPCRType :=
        (Sail.BitVec.updateSubrange fpcr 0 0 (Sail.BitVec.extractLsb 0b11#2 1 1))
      (Sail.BitVec.updateSubrange fpcr 24 24 (Sail.BitVec.extractLsb 0b11#2 0 0)))
    else fpcr
  let w__3 ← (( do (FPUnpack__1 operand fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__3 : (FPType × (BitVec 1) × real))
  let fptype : FPType := tup__0
  let sign : (BitVec 1) := tup__1
  let value_name : real := tup__2
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1119)
      (Sail.BitVec.length operand))) ) : SailM (BitVec k_N) )
  if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
  then
    (do
      (FPProcessNaN__1 fptype operand fpcr fpexc))
  else
    (do
      if ((BEq.beq fptype FPType_Zero) : Bool)
      then
        (do
          let w__5 ← (( do
            ((Sail.BitVec.castWidth ) <$> (FPInfinity sign (Sail.BitVec.length result))) ) : SailM
            (BitVec k_N) )
          let result := (w__5 : (BitVec k_N))
          if (fpexc : Bool)
          then
            (do
              (FPProcessException FPExc_DivideByZero fpcr))
          else (pure (()))
          (pure (result)))
      else
        (do
          if ((sign == 1#1) : Bool)
          then
            (do
              let w__6 ← (( do
                ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))) )
                : SailM (BitVec k_N) )
              let result := (w__6 : (BitVec k_N))
              if (fpexc : Bool)
              then
                (do
                  (FPProcessException FPExc_InvalidOp fpcr))
              else (pure (()))
              (pure (result)))
          else
            (do
              if ((BEq.beq fptype FPType_Infinity) : Bool)
              then
                (do
                  ((Sail.BitVec.castWidth ) <$> (FPZero 0#1 (Sail.BitVec.length result))))
              else
                (do
                  let fraction ← (( do (undefined_bitvector_at (← occLabel 1120) 52) ) : SailM
                    (BitVec 52) )
                  let exp ← (( do (undefined_int_at (← occLabel 1121) ()) ) : SailM Int )
                  let (exp, fraction) : (Int × (BitVec 52)) :=
                    match (Sail.BitVec.length result) with
                    | 16 =>
                      (let fraction : (BitVec 52) :=
                        ((Sail.BitVec.extractLsb operand 9 0) +++ (Zeros (n := 42)))
                      let exp : Int := (BitVec.toNat (Sail.BitVec.extractLsb operand 14 10))
                      (exp, fraction))
                    | 32 =>
                      (let fraction : (BitVec 52) :=
                        ((Sail.BitVec.extractLsb operand 22 0) +++ (Zeros (n := 29)))
                      let exp : Int := (BitVec.toNat (Sail.BitVec.extractLsb operand 30 23))
                      (exp, fraction))
                    | 64 =>
                      (let fraction : (BitVec 52) := (Sail.BitVec.extractLsb operand 51 0)
                      let exp : Int := (BitVec.toNat (Sail.BitVec.extractLsb operand 62 52))
                      (exp, fraction))
                    | _ => (exp, fraction)
                  let (exp, fraction) ← (( do
                    if ((exp == 0) : Bool)
                    then
                      (do
                        let (exp, fraction) ← (( do
                          let loop_vars ← sailWhileFuelM (fuel := 1048576) (fun (exp, fraction) => (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                  fraction 51)])) == 0#1))) (exp, fraction)
                            fun (exp, fraction) => do
                              (pure (let fraction : (BitVec 52) :=
                                  ((Sail.BitVec.extractLsb fraction 50 0) +++ 0#1)
                                let exp : Int := (exp -i 1)
                                (exp, fraction) : (Int × (BitVec 52))))
                          (pure loop_vars) ) : SailM (Int × (BitVec 52)) )
                        let fraction : (BitVec 52) :=
                          ((Sail.BitVec.extractLsb fraction 50 0) +++ 0#1)
                        (pure (exp, fraction)))
                    else (pure (exp, fraction)) ) : SailM (Int × (BitVec 52)) )
                  let fraction := fraction
                  let exp : Int := exp
                  let scaled ← (( do
                    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 1122)
                      0 4095))) ) : SailM Nat )
                  let increasedprecision_name ← (( do
                    (pure ((← do
                          if ((((Sail.BitVec.length result) == 32) : Bool) : Bool)
                          then
                            (do
                              (HaveFeatRPRES ()))
                          else (pure false)) && altfp)) ) : SailM Bool )
                  let scaled : Nat :=
                    if ((! increasedprecision_name) : Bool)
                    then
                      (if (((BitVec.setWidth 1 (BitVec.join1 [(integer_access exp 0)])) == 0#1) : Bool)
                      then (BitVec.toNat (1#1 +++ (Sail.BitVec.extractLsb fraction 51 44)))
                      else (BitVec.toNat (0b01#2 +++ (Sail.BitVec.extractLsb fraction 51 45))))
                    else
                      (if (((BitVec.setWidth 1 (BitVec.join1 [(integer_access exp 0)])) == 0#1) : Bool)
                      then (BitVec.toNat (1#1 +++ (Sail.BitVec.extractLsb fraction 51 41)))
                      else (BitVec.toNat (0b01#2 +++ (Sail.BitVec.extractLsb fraction 51 42))))
                  let scaled : Int := scaled
                  let result_exp ← (( do (undefined_int_at (← occLabel 1123) ()) ) : SailM Int )
                  let result_exp : Int :=
                    match (Sail.BitVec.length result) with
                    | 16 => (fdiv_int (44 -i exp) 2)
                    | 32 => (fdiv_int (380 -i exp) 2)
                    | 64 => (fdiv_int (3068 -i exp) 2)
                    | _ => result_exp
                  let result_exp : Int := result_exp
                  let estimate ← (( do (RecipSqrtEstimate scaled increasedprecision_name) ) :
                    SailM Int )
                  let result : (BitVec k_N) :=
                    match (Sail.BitVec.length result) with
                    | 16 =>
                      (Sail.BitVec.castWidth (((0#1 +++ (integer_subrange result_exp
                              ((Sail.BitVec.length result) -i 12) 0)) +++ (integer_subrange estimate
                            7 0)) +++ (Zeros (n := 2))))
                    | 32 =>
                      (if ((! increasedprecision_name) : Bool)
                      then
                        (Sail.BitVec.castWidth (((0#1 +++ (integer_subrange result_exp
                                ((Sail.BitVec.length result) -i 25) 0)) +++ (integer_subrange
                              estimate 7 0)) +++ (Zeros (n := 15))))
                      else
                        (Sail.BitVec.castWidth (((0#1 +++ (integer_subrange result_exp
                                ((Sail.BitVec.length result) -i 25) 0)) +++ (integer_subrange
                              estimate 11 0)) +++ (Zeros (n := 11)))))
                    | 64 =>
                      (Sail.BitVec.castWidth (((0#1 +++ (integer_subrange result_exp
                              ((Sail.BitVec.length result) -i 54) 0)) +++ (integer_subrange estimate
                            7 0)) +++ (Zeros (n := 44))))
                    | _ => result
                  (pure (result))))))


/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, List.elem k_N [16, 32, 64] -/
def FPSub__1 (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (BitVec k_N) := do
  let done ← (( do (undefined_bool_at (← occLabel 1128) ()) ) : SailM Bool )
  let inf1 ← (( do (undefined_bool_at (← occLabel 1129) ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool_at (← occLabel 1130) ()) ) : SailM Bool )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1131)
      (Sail.BitVec.length op2))) ) : SailM (BitVec k_N) )
  let result_sign ← (( do (undefined_bitvector_at (← occLabel 1132) 1) ) : SailM (BitVec 1) )
  let result_value ← (( do (undefined_real_at (← occLabel 1133) ()) ) : SailM real )
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 1134) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 1135) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 1136) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 1137) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 1138) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 1139) ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool_at (← occLabel 1140) ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool_at (← occLabel 1141) ()) ) : SailM Bool )
  ArmFull.assert (((Sail.BitVec.length result) == 16) || (((Sail.BitVec.length result) == 32) || ((Sail.BitVec.length
          result) == 64))) "sail-arm/v8_base.sail:17770.41-17770.42"
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let w__0 ← (( do (FPUnpack__1 op1 fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let type1 : FPType := tup__0
  let sign1 : (BitVec 1) := tup__1
  let value1_name : real := tup__2
  let w__1 ← (( do (FPUnpack__1 op2 fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let type2 : FPType := tup__0
  let sign2 : (BitVec 1) := tup__1
  let value2_name : real := tup__2
  let w__2 ← (( do (FPProcessNaNs__1 type1 type2 op1 op2 fpcr fpexc) ) : SailM
    (Bool × (BitVec k_N)) )
  let (tup__0, tup__1) := (w__2 : (Bool × (BitVec k_N)))
  let done : Bool := tup__0
  let result : (BitVec k_N) := tup__1
  if ((! done) : Bool)
  then
    (do
      let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
      let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
      let zero1 : Bool := (BEq.beq type1 FPType_Zero)
      let zero2 : Bool := (BEq.beq type2 FPType_Zero)
      let result ← (( do
        if (((inf1 && inf2) && (sign1 == sign2)) : Bool)
        then
          (do
            let w__3 ← (( do
              ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))) ) :
              SailM (BitVec k_N) )
            let result := (w__3 : (BitVec k_N))
            if (fpexc : Bool)
            then
              (do
                (FPProcessException FPExc_InvalidOp fpcr))
            else (pure (()))
            (pure (result)))
        else
          (do
            if (((inf1 && (sign1 == 0#1)) || (inf2 && (sign2 == 1#1))) : Bool)
            then
              (do
                ((Sail.BitVec.castWidth ) <$> (FPInfinity 0#1 (Sail.BitVec.length result))))
            else
              (do
                if (((inf1 && (sign1 == 1#1)) || (inf2 && (sign2 == 0#1))) : Bool)
                then
                  (do
                    ((Sail.BitVec.castWidth ) <$> (FPInfinity 1#1 (Sail.BitVec.length result))))
                else
                  (do
                    if (((zero1 && zero2) && (sign1 == (Complement.complement sign2))) : Bool)
                    then
                      (do
                        ((Sail.BitVec.castWidth ) <$> (FPZero sign1 (Sail.BitVec.length result))))
                    else
                      (do
                        let result_value : real := (sub_real value1_name value2_name)
                        if ((eq_real result_value (0)) : Bool)
                        then
                          (do
                            let result_sign : (BitVec 1) :=
                              if ((BEq.beq rounding FPRounding_NEGINF) : Bool)
                              then 1#1
                              else 0#1
                            ((Sail.BitVec.castWidth ) <$> (FPZero result_sign
                              (Sail.BitVec.length result))))
                        else
                          (do
                            ((Sail.BitVec.castWidth ) <$> (FPRound__2 result_value fpcr rounding
                              fpexc (Sail.BitVec.length result)))))))) ) : SailM (BitVec k_N) )
      if (fpexc : Bool)
      then
        (do
          (FPProcessDenorms type1 type2 (Sail.BitVec.length result) fpcr))
      else (pure (()))
      (pure (result)))
  else (pure (result))


/-- Type quantifiers: M : Nat, k_N : Nat, fbits : Int, k_is_unsigned : Bool, List.elem k_N
  [16, 32, 64] ∧ List.elem M [16, 32, 64] -/
def FPToFixed (op : (BitVec k_N)) (fbits : Int) (is_unsigned : Bool) (fpcr : (BitVec 64)) (rounding : FPRounding) (M : Nat) : SailM (BitVec M) := do
  let fptype ← (( do (undefined_FPType (← occLabel 1142) ()) ) : SailM FPType )
  let overflow ← (( do (undefined_bool_at (← occLabel 1143) ()) ) : SailM Bool )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1144)
      (Sail.Int.toNatChecked (M)))) ) : SailM (BitVec M) )
  let sign ← (( do (undefined_bitvector_at (← occLabel 1145) 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real_at (← occLabel 1146) ()) ) : SailM real )
  ArmFull.assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length
          op) == 64))) "sail-arm/v8_base.sail:17844.41-17844.42"
  ArmFull.assert ((M == 16) || ((M == 32) || (M == 64))) "sail-arm/v8_base.sail:17845.38-17845.39"
  ArmFull.assert (fbits ≥b 0) "sail-arm/v8_base.sail:17846.21-17846.22"
  ArmFull.assert (bne rounding FPRounding_ODD) "sail-arm/v8_base.sail:17847.37-17847.38"
  let altfp ← (( do
    (pure ((← do
          if ((← do
               (HaveAltFP ())) : Bool)
          then
            (do
              let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              (pure (((! w__1) : Bool))))
          else (pure false)) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  let fpexc : Bool := (! altfp)
  let w__3 ← (( do (FPUnpack__1 op fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__3 : (FPType × (BitVec 1) × real))
  let fptype : FPType := tup__0
  let sign : (BitVec 1) := tup__1
  let value_name : real := tup__2
  if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
  then
    (do
      (FPProcessException FPExc_InvalidOp fpcr))
  else (pure (()))
  let value_name : real := (mult_real value_name (real_power (2) fbits))
  let int_result : Int := (round_down value_name)
  let error : real := (sub_real value_name (to_real int_result))
  let round_up ← (( do (undefined_bool_at (← occLabel 1147) ()) ) : SailM Bool )
  let round_up : Bool :=
    match rounding with
    | .FPRounding_TIEEVEN =>
      ((gt_real error (1/2)) || ((eq_real error (1/2)) && ((BitVec.setWidth 1 (BitVec.join1 [(integer_access
                int_result 0)])) == 1#1)))
    | .FPRounding_POSINF => (bne error (0))
    | .FPRounding_NEGINF => false
    | .FPRounding_ZERO => ((bne error (0)) && (int_result <b 0))
    | .FPRounding_TIEAWAY =>
      ((gt_real error (1/2)) || ((eq_real error (1/2)) && (int_result ≥b 0)))
    | _ => round_up
  let int_result : Int :=
    if (round_up : Bool)
    then (int_result +i 1)
    else int_result
  let int_result : Int := int_result
  let w__4 ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ int_result M is_unsigned)) ) :
    SailM ((BitVec M) × Bool) )
  let (tup__0, tup__1) := (w__4 : ((BitVec M) × Bool))
  let result : (BitVec M) := tup__0
  let overflow : Bool := tup__1
  if (overflow : Bool)
  then
    (do
      (FPProcessException FPExc_InvalidOp fpcr))
  else
    (do
      if ((bne error (0)) : Bool)
      then
        (do
          (FPProcessException FPExc_Inexact fpcr))
      else (pure (())))
  (pure ((Sail.BitVec.castWidth result)))


/-- Type quantifiers: k_Is64 : Bool, k_M : Nat, N : Nat, k_M = 64 ∧ N = 32 -/
def FPToFixedJS (op : (BitVec k_M)) (fpcr : (BitVec 64)) (Is64 : Bool) (N : Nat) : SailM ((BitVec N) × (BitVec 1)) := do
  let fptype ← (( do (undefined_FPType (← occLabel 1148) ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector_at (← occLabel 1149) 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real_at (← occLabel 1150) ()) ) : SailM real )
  ArmFull.assert (((Sail.BitVec.length op) == 64) && (N == 32)) "sail-arm/v8_base.sail:17897.29-17897.30"
  let w__3 ← (( do
    (pure ((← do
          if ((← do
               (HaveAltFP ())) : Bool)
          then
            (do
              let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              (pure (((! w__1) : Bool))))
          else (pure false)) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  let fpexc_idenorm : Bool := (! w__3)
  let w__4 ← (( do (FPUnpack__1 op fpcr fpexc_idenorm) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__4 : (FPType × (BitVec 1) × real))
  let fptype : FPType := tup__0
  let sign : (BitVec 1) := tup__1
  let value_name : real := tup__2
  let z : (BitVec 1) := 1#1
  let z ← (( do
    if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
    then
      (do
        (FPProcessException FPExc_InvalidOp fpcr)
        (pure (0#1)))
    else (pure (z)) ) : SailM (BitVec 1) )
  let int_result : Int := (round_down value_name)
  let error : real := (sub_real value_name (to_real int_result))
  let round_it_up : Bool := ((bne error (0)) && (int_result <b 0))
  let int_result : Int :=
    if (round_it_up : Bool)
    then (int_result +i 1)
    else int_result
  let int_result : Int := int_result
  let result ← (( do (undefined_int_at (← occLabel 1151) ()) ) : SailM Int )
  let result : Int :=
    if ((int_result <b 0) : Bool)
    then
      (int_result -i ((2 ^i 32) *i (round_up (div_real (to_real int_result) (to_real (2 ^i 32))))))
    else
      (int_result -i ((2 ^i 32) *i (round_down (div_real (to_real int_result) (to_real (2 ^i 32))))))
  let z ← (( do
    if (((int_result <b (Neg.neg (2 ^i 31))) || (int_result >b ((2 ^i 31) -i 1))) : Bool)
    then
      (do
        (FPProcessException FPExc_InvalidOp fpcr)
        (pure (0#1)))
    else
      (do
        if ((bne error (0)) : Bool)
        then
          (do
            (FPProcessException FPExc_Inexact fpcr)
            (pure (0#1)))
        else
          (let z : (BitVec 1) :=
            if (((sign == 1#1) && (eq_real value_name (0))) : Bool)
            then 0#1
            else
              (if ((((sign == 0#1) && (eq_real value_name (0))) && (! (IsZero
                       (Sail.BitVec.extractLsb op 51 0)))) : Bool)
              then 0#1
              else z)
          (pure (z)))) ) : SailM (BitVec 1) )
  let result : Int :=
    if ((BEq.beq fptype FPType_Infinity) : Bool)
    then 0
    else result
  let result : Int := result
  (pure (((Sail.BitVec.castWidth (integer_subrange result (N -i 1) 0)), z)))


/-- Type quantifiers: k_aligned : Bool, k_ispair : Bool, size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def AArch64_MemSingle_read__1 (address : (BitVec 64)) (size : Nat) (accdesc_in : AccessDescriptor) (aligned : Bool) (ispair : Bool) : SailM (BitVec (size * 8)) := do
  ArmFull.assert ((size == 1) || ((size == 2) || ((size == 4) || ((size == 8) || (size == 16))))) "sail-arm/v8_base.sail:27977.69-27977.70"
  let value_name ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1631)
      (Sail.Int.toNatChecked ((size *i 8))))) ) : SailM (BitVec (size * 8)) )
  let accdesc : AccessDescriptor := accdesc_in
  let w__0 ← (( do (HaveLSE2Ext ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (AllInAlignedQuantity address size 16) ) : SailM Bool )
      ArmFull.assert w__1 "sail-arm/v8_base.sail:27981.54-27981.55")
  else
    (do
      ArmFull.assert (IsAligned__1 address size) "sail-arm/v8_base.sail:27983.42-27983.43")
  let w__3 ← (( do
    (pure ((← do
          (HaveMTE2Ext ())) && (accdesc.tagchecked : Bool))) ) : SailM Bool )
  let accdesc ← (( do
    if (w__3 : Bool)
    then
      (do
        let w__4 ← (( do (AArch64_AccessIsTagChecked address accdesc) ) : SailM Bool )
        let accdesc := ({ accdesc with tagchecked := w__4 } : AccessDescriptor)
        (pure (accdesc)))
    else (pure (accdesc)) ) : SailM AccessDescriptor )
  let memaddrdesc ← (( do (AArch64_TranslateAddress address accdesc aligned size) ) : SailM
    AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then
    (do
      (AArch64_Abort address memaddrdesc.fault))
  else (pure (()))
  let w__5 ← (( do (HaveTME ()) ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      let w__7 ← (( do
        if ((accdesc.transactional : Bool) : Bool)
        then
          (do
            let w__6 ← (( do (MemHasTransactionalAccess memaddrdesc.memattrs) ) : SailM Bool )
            (pure (((! w__6) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__7 : Bool)
      then
        (do
          (FailTransaction TMFailure_IMP false))
      else (pure (())))
  else (pure (()))
  let w__9 ← (( do
    (pure ((← do
          (HaveMTE2Ext ())) && (accdesc.tagchecked : Bool))) ) : SailM Bool )
  if (w__9 : Bool)
  then
    (do
      let ptag : (BitVec 4) := (AArch64_PhysicalTag address)
      let w__10 ← (( do (AArch64_CheckTag memaddrdesc accdesc ptag) ) : SailM Bool )
      if ((! w__10) : Bool)
      then
        (do
          (AArch64_TagCheckFault address accdesc))
      else (pure (())))
  else (pure (()))
  let w__11 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__11 : Bool)
  then
    (do
      let is_load : Bool := true
      (SPESampleLoadStore is_load accdesc memaddrdesc))
  else (pure (()))
  let atomic ← (( do (undefined_bool_at (← occLabel 1632) ()) ) : SailM Bool )
  let atomic ← (( do
    if ((((BEq.beq memaddrdesc.memattrs.memtype MemType_Normal) && (memaddrdesc.memattrs.inner.attrs == MemAttr_WB)) && (memaddrdesc.memattrs.outer.attrs == MemAttr_WB)) : Bool)
    then (pure (true))
    else
      (do
        if (((((accdesc.exclusive || accdesc.atomicop) || accdesc.acqsc) || accdesc.acqpc) || accdesc.relsc) : Bool)
        then
          (do
            let w__13 ← (( do
              if (((! aligned) : Bool) : Bool)
              then
                (do
                  let w__12 ← (( do (ConstrainUnpredictableBool Unpredictable_MISALIGNEDATOMIC) )
                    : SailM Bool )
                  (pure (((! w__12) : Bool))))
              else (pure false) ) : SailM Bool )
            if (w__13 : Bool)
            then
              (do
                let w__14 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
                (AArch64_Abort address w__14)
                (pure (atomic)))
            else (pure (true)))
        else
          (do
            if (aligned : Bool)
            then
              (let atomic : Bool := (! ispair)
              (pure (atomic)))
            else
              (do
                (__IMPDEF_boolean "FEAT_LSE2: access is atomic")))) ) : SailM Bool )
  let memstatus ← (( do (undefined_PhysMemRetStatus (← occLabel 1633) ()) ) : SailM
    PhysMemRetStatus )
  if (atomic : Bool)
  then
    (do
      let w__16 ← (( do
        ((fun (x0, x1) => (x0, (Sail.BitVec.castWidth x1))) <$> (PhysMemRead memaddrdesc size
          accdesc none)) ) : SailM (PhysMemRetStatus × (BitVec (8 * size))) )
      let (tup__0, tup__1) := (w__16 : (PhysMemRetStatus × (BitVec (8 * size))))
      let memstatus : PhysMemRetStatus := tup__0
      let value_name : (BitVec (size * 8)) := (Sail.BitVec.castWidth tup__1)
      if ((IsFault__2 memstatus) : Bool)
      then
        (do
          (HandleExternalReadAbort memstatus memaddrdesc size accdesc))
      else (pure (()))
      (pure (value_name)))
  else
    (do
      if ((aligned && ispair) : Bool)
      then
        (do
          ArmFull.assert ((size == 8) || (size == 16)) "sail-arm/v8_base.sail:28031.37-28031.38"
          let halfsize : Nat := (Sail.Int.toNatChecked ((Int.ediv size 2)))
          let highhalf ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1634)
              (Sail.Int.toNatChecked ((halfsize *i 8))))) ) : SailM
            (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) )
          let lowhalf ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1635)
              (Sail.Int.toNatChecked ((halfsize *i 8))))) ) : SailM
            (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) )
          let w__17 ← (( do
            ((fun (x0, x1) => (x0, (Sail.BitVec.castWidth x1))) <$> (PhysMemRead memaddrdesc
              halfsize accdesc none)) ) : SailM
            (PhysMemRetStatus × (BitVec (8 * (Sail.Int.toNatChecked halfsize)))) )
          let (tup__0, tup__1) :=
            (w__17 : (PhysMemRetStatus × (BitVec (8 * (Sail.Int.toNatChecked halfsize)))))
          let memstatus : PhysMemRetStatus := tup__0
          let lowhalf : (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) :=
            (Sail.BitVec.castWidth tup__1)
          if ((IsFault__2 memstatus) : Bool)
          then
            (do
              (HandleExternalReadAbort memstatus memaddrdesc halfsize accdesc))
          else (pure (()))
          let memaddrdesc : AddressDescriptor :=
            { memaddrdesc with paddress := { memaddrdesc.paddress with address := (BitVec.addInt
                  memaddrdesc.paddress.address halfsize) } }
          let w__18 ← (( do
            ((fun (x0, x1) => (x0, (Sail.BitVec.castWidth x1))) <$> (PhysMemRead memaddrdesc
              halfsize accdesc none)) ) : SailM
            (PhysMemRetStatus × (BitVec (8 * (Sail.Int.toNatChecked halfsize)))) )
          let (tup__0, tup__1) :=
            (w__18 : (PhysMemRetStatus × (BitVec (8 * (Sail.Int.toNatChecked halfsize)))))
          let memstatus : PhysMemRetStatus := tup__0
          let highhalf : (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) :=
            (Sail.BitVec.castWidth tup__1)
          if ((IsFault__2 memstatus) : Bool)
          then
            (do
              (HandleExternalReadAbort memstatus memaddrdesc halfsize accdesc))
          else (pure (()))
          let value_name : (BitVec (size * 8)) := (Sail.BitVec.castWidth (highhalf +++ lowhalf))
          (pure (value_name)))
      else
        (do
          let (memaddrdesc, memstatus, value_name) ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := (Sail.Int.toNatChecked ((size -i 1)))
            (do
              let mut loop_vars := (memaddrdesc, memstatus, value_name)
              for i in [loop_i_lower:loop_i_upper:1]i do
                let (memaddrdesc, memstatus, value_name) := loop_vars
                loop_vars ← do
                  let w__19 ← (( do (PhysMemRead memaddrdesc 1 accdesc none) ) : SailM
                    (PhysMemRetStatus × (BitVec (8 * 1))) )
                  let (tup__0, tup__1) := (w__19 : (PhysMemRetStatus × (BitVec (8 * 1))))
                  let memstatus : PhysMemRetStatus := tup__0
                  let value_name : (BitVec (size * 8)) :=
                    (Sail.BitVec.updateSubrange value_name (Sail.Int.toNatChecked (((8 *i i) +i 7)))
                      (Sail.Int.toNatChecked ((8 *i i))) (Sail.BitVec.castWidth tup__1))
                  if ((IsFault__2 memstatus) : Bool)
                  then
                    (do
                      (HandleExternalReadAbort memstatus memaddrdesc 1 accdesc))
                  else (pure (()))
                  let memaddrdesc : AddressDescriptor :=
                    { memaddrdesc with paddress := { memaddrdesc.paddress with address := (BitVec.addInt
                          memaddrdesc.paddress.address 1) } }
                  (pure ((memaddrdesc, memstatus, value_name)))
              (pure loop_vars)) ) : SailM
            (AddressDescriptor × PhysMemRetStatus × (BitVec (size * 8))) )
          (pure (value_name))))


end ArmFull.Functions
