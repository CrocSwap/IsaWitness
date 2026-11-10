import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0015
import ArmFull.Fn.M0018
import ArmFull.Fn.M0019
import ArmFull.Fn.M0087
import ArmFull.Fn.M0099
import ArmFull.Fn.M0115
import ArmFull.Fn.M0116
import ArmFull.Fn.M0145
import ArmFull.Fn.M0153
import ArmFull.Fn.M0167
import ArmFull.Fn.M0178
import ArmFull.Fn.M0840
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

/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, k_N = 32 -/
def FPMulAddH__1 (addend : (BitVec k_N)) (op1 : (BitVec (k_N / 2))) (op2 : (BitVec (k_N / 2))) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (BitVec k_N) := do
  let done ← (( do (undefined_bool_at (← occLabel 1062) ()) ) : SailM Bool )
  let infA ← (( do (undefined_bool_at (← occLabel 1063) ()) ) : SailM Bool )
  let infP ← (( do (undefined_bool_at (← occLabel 1064) ()) ) : SailM Bool )
  let invalidop ← (( do (undefined_bool_at (← occLabel 1065) ()) ) : SailM Bool )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1066)
      (Sail.BitVec.length addend))) ) : SailM (BitVec k_N) )
  let result_sign ← (( do (undefined_bitvector_at (← occLabel 1067) 1) ) : SailM (BitVec 1) )
  let result_value ← (( do (undefined_real_at (← occLabel 1068) ()) ) : SailM real )
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 1069) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 1070) 1) ) : SailM (BitVec 1) )
  let signA ← (( do (undefined_bitvector_at (← occLabel 1071) 1) ) : SailM (BitVec 1) )
  let signP ← (( do (undefined_bitvector_at (← occLabel 1072) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 1073) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 1074) ()) ) : SailM FPType )
  let typeA ← (( do (undefined_FPType (← occLabel 1075) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 1076) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 1077) ()) ) : SailM real )
  let valueA_name ← (( do (undefined_real_at (← occLabel 1078) ()) ) : SailM real )
  let zeroA ← (( do (undefined_bool_at (← occLabel 1079) ()) ) : SailM Bool )
  let zeroP ← (( do (undefined_bool_at (← occLabel 1080) ()) ) : SailM Bool )
  ArmFull.assert ((Sail.BitVec.length result) == 32) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:17149.19-17149.20"
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let w__0 ← (( do (FPUnpack__1 addend fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let typeA : FPType := tup__0
  let signA : (BitVec 1) := tup__1
  let valueA_name : real := tup__2
  let w__1 ← (( do (FPUnpack__1 op1 fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let type1 : FPType := tup__0
  let sign1 : (BitVec 1) := tup__1
  let value1_name : real := tup__2
  let w__2 ← (( do (FPUnpack__1 op2 fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__2 : (FPType × (BitVec 1) × real))
  let type2 : FPType := tup__0
  let sign2 : (BitVec 1) := tup__1
  let value2_name : real := tup__2
  let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
  let zero1 : Bool := (BEq.beq type1 FPType_Zero)
  let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
  let zero2 : Bool := (BEq.beq type2 FPType_Zero)
  let w__3 ← (( do (FPProcessNaNs3H typeA type1 type2 addend op1 op2 fpcr fpexc) ) : SailM
    (Bool × (BitVec k_N)) )
  let (tup__0, tup__1) := (w__3 : (Bool × (BitVec k_N)))
  let done : Bool := tup__0
  let result : (BitVec k_N) := tup__1
  let w__7 ← (( do
    (pure ((← do
          if ((← do
               (HaveAltFP ())) : Bool)
          then
            (do
              let w__5 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              (pure (((! w__5) : Bool))))
          else (pure false)) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  let result ← (( do
    if ((! w__7) : Bool)
    then
      (do
        if (((BEq.beq typeA FPType_QNaN) && ((inf1 && zero2) || (zero1 && inf2))) : Bool)
        then
          (do
            let w__8 ← (( do
              ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))) ) :
              SailM (BitVec k_N) )
            let result := (w__8 : (BitVec k_N))
            if (fpexc : Bool)
            then
              (do
                (FPProcessException FPExc_InvalidOp fpcr))
            else (pure (()))
            (pure (result)))
        else (pure (result)))
    else (pure (result)) ) : SailM (BitVec k_N) )
  if ((! done) : Bool)
  then
    (do
      let infA : Bool := (BEq.beq typeA FPType_Infinity)
      let zeroA : Bool := (BEq.beq typeA FPType_Zero)
      let signP : (BitVec 1) := (sign1 ^^^ sign2)
      let infP : Bool := (inf1 || inf2)
      let zeroP : Bool := (zero1 || zero2)
      let invalidop : Bool :=
        (((inf1 && zero2) || (zero1 && inf2)) || ((infA && infP) && (signA != signP)))
      let result ← (( do
        if (invalidop : Bool)
        then
          (do
            let w__9 ← (( do
              ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))) ) :
              SailM (BitVec k_N) )
            let result := (w__9 : (BitVec k_N))
            if (fpexc : Bool)
            then
              (do
                (FPProcessException FPExc_InvalidOp fpcr))
            else (pure (()))
            (pure (result)))
        else
          (do
            if (((infA && (signA == 0#1)) || (infP && (signP == 0#1))) : Bool)
            then
              (do
                ((Sail.BitVec.castWidth ) <$> (FPInfinity 0#1 (Sail.BitVec.length result))))
            else
              (do
                if (((infA && (signA == 1#1)) || (infP && (signP == 1#1))) : Bool)
                then
                  (do
                    ((Sail.BitVec.castWidth ) <$> (FPInfinity 1#1 (Sail.BitVec.length result))))
                else
                  (do
                    if (((zeroA && zeroP) && (signA == signP)) : Bool)
                    then
                      (do
                        ((Sail.BitVec.castWidth ) <$> (FPZero signA (Sail.BitVec.length result))))
                    else
                      (do
                        let result_value : real :=
                          (add_real valueA_name (mult_real value1_name value2_name))
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
      if (((! invalidop) && fpexc) : Bool)
      then
        (do
          (FPProcessDenorm typeA (Sail.BitVec.length result) fpcr))
      else (pure (()))
      (pure (result)))
  else (pure (result))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPNeg (op : (BitVec k_N)) : SailM (BitVec k_N) := SailME.run do
  let fptype ← (( do (undefined_FPType (← occLabel 1081) ()) ) : SailME (BitVec k_N) FPType )
  ArmFull.assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length
          op) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:17222.41-17222.42"
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (UsingAArch32 ()) ) : SailME (BitVec k_N) Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        (HaveAltFP ()))
    else (pure false) ) : SailME (BitVec k_N) Bool )
  if (w__2 : Bool)
  then
    (do
      let fpcr ← (( do (FPCR_read ()) ) : SailME (BitVec k_N) FPCRType )
      if (((_get_FPCRType_AH fpcr) == 1#1) : Bool)
      then
        (do
          let (__tup_0, _, _) ← (( do (FPUnpack__1 op fpcr false) ) : SailME (BitVec k_N)
            (FPType × (BitVec 1) × real) )
          let fptype : FPType := __tup_0
          if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
          then
            (do
              SailME.throw (op : (BitVec k_N)))
          else (pure (())))
      else (pure (())))
  else (pure (()))
  (pure ((Sail.BitVec.castWidth ((Complement.complement
        (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op
            (Sail.Int.toNatChecked (((Sail.BitVec.length op) -i 1))))]))) +++ (Sail.BitVec.extractLsb
        op (Sail.Int.toNatChecked (((Sail.BitVec.length op) -i 2))) 0)))))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPRecipEstimate (operand : (BitVec k_N)) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  let estimate ← (( do (undefined_int_at (← occLabel 1082) ()) ) : SailM Int )
  let fptype ← (( do (undefined_FPType (← occLabel 1083) ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector_at (← occLabel 1084) 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real_at (← occLabel 1085) ()) ) : SailM real )
  ArmFull.assert (((Sail.BitVec.length operand) == 16) || (((Sail.BitVec.length operand) == 32) || ((Sail.BitVec.length
          operand) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:17267.41-17267.42"
  let fpcr : FPCRType := fpcr_in
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1086)
      (Sail.BitVec.length operand))) ) : SailM (BitVec k_N) )
  let overflow_to_inf ← (( do (undefined_bool_at (← occLabel 1087) ()) ) : SailM Bool )
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
  let fpcr : (BitVec 64) :=
    if (altfp : Bool)
    then (Sail.BitVec.updateSubrange fpcr 23 22 0b00#2)
    else fpcr
  let w__3 ← (( do (FPUnpack__1 operand fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__3 : (FPType × (BitVec 1) × real))
  let fptype : FPType := tup__0
  let sign : (BitVec 1) := tup__1
  let value_name : real := tup__2
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
  then
    (do
      (FPProcessNaN__1 fptype operand fpcr fpexc))
  else
    (do
      if ((BEq.beq fptype FPType_Infinity) : Bool)
      then
        (do
          ((Sail.BitVec.castWidth ) <$> (FPZero sign (Sail.BitVec.length result))))
      else
        (do
          if ((BEq.beq fptype FPType_Zero) : Bool)
          then
            (do
              let w__6 ← (( do
                ((Sail.BitVec.castWidth ) <$> (FPInfinity sign (Sail.BitVec.length result))) ) :
                SailM (BitVec k_N) )
              let result := (w__6 : (BitVec k_N))
              if (fpexc : Bool)
              then
                (do
                  (FPProcessException FPExc_DivideByZero fpcr))
              else (pure (()))
              (pure (result)))
          else
            (do
              if ((((((Sail.BitVec.length result) == 16) && (lt_real (abs_real value_name)
                         (real_power (2) (Neg.neg 16)))) || (((Sail.BitVec.length result) == 32) && (lt_real
                         (abs_real value_name) (real_power (2) (Neg.neg 128))))) || (((Sail.BitVec.length
                         result) == 64) && (lt_real (abs_real value_name)
                       (real_power (2) (Neg.neg 1024))))) : Bool)
              then
                (do
                  let overflow_to_inf : Bool :=
                    match rounding with
                    | .FPRounding_TIEEVEN => true
                    | .FPRounding_POSINF => (sign == 0#1)
                    | .FPRounding_NEGINF => (sign == 1#1)
                    | .FPRounding_ZERO => false
                    | _ => overflow_to_inf
                  let w__9 ← (( do
                    if (overflow_to_inf : Bool)
                    then
                      (do
                        ((Sail.BitVec.castWidth ) <$> (FPInfinity sign (Sail.BitVec.length result))))
                    else
                      (do
                        ((Sail.BitVec.castWidth ) <$> (FPMaxNormal sign (Sail.BitVec.length result))))
                    ) : SailM (BitVec k_N) )
                  let result := (w__9 : (BitVec k_N))
                  if (fpexc : Bool)
                  then
                    (do
                      (FPProcessException FPExc_Overflow fpcr)
                      (FPProcessException FPExc_Inexact fpcr))
                  else (pure (()))
                  (pure (result)))
              else
                (do
                  if ((((((_get_FPCRType_FZ fpcr) == 1#1) && ((Sail.BitVec.length result) != 16)) || (((_get_FPCRType_FZ16
                               fpcr) == 1#1) && ((Sail.BitVec.length result) == 16))) && (((((Sail.BitVec.length
                                 result) == 16) && (gteq_real (abs_real value_name)
                               (real_power (2) 14))) || (((Sail.BitVec.length result) == 32) && (gteq_real
                               (abs_real value_name) (real_power (2) 126)))) || (((Sail.BitVec.length
                               result) == 64) && (gteq_real (abs_real value_name)
                             (real_power (2) 1022))))) : Bool)
                  then
                    (do
                      let w__10 ← (( do
                        ((Sail.BitVec.castWidth ) <$> (FPZero sign (Sail.BitVec.length result))) ) :
                        SailM (BitVec k_N) )
                      let result := (w__10 : (BitVec k_N))
                      let w__11 ← (( do (UsingAArch32 ()) ) : SailM Bool )
                      if (w__11 : Bool)
                      then
                        (do
                          let w__12 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
                          (FPSCR_write (_update_FPSCR_Type_UFC w__12 1#1)))
                      else
                        (do
                          if (fpexc : Bool)
                          then
                            (do
                              let w__13 ← (( do readReg FPSR ) : SailM (BitVec 64) )
                              writeReg FPSR (Sail.BitVec.updateSubrange w__13 3 3 1#1))
                          else (pure (())))
                      (pure (result)))
                  else
                    (do
                      let fraction ← (( do (undefined_bitvector_at (← occLabel 1088) 52) ) :
                        SailM (BitVec 52) )
                      let exp ← (( do (undefined_int_at (← occLabel 1089) ()) ) : SailM Int )
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
                      let (exp, fraction) : (Int × (BitVec 52)) :=
                        if ((exp == 0) : Bool)
                        then
                          (let (exp, fraction) : (Int × (BitVec 52)) :=
                            if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access fraction 51)])) == 0#1) : Bool)
                            then
                              (let exp : Int := (Neg.neg 1)
                              let fraction : (BitVec 52) :=
                                ((Sail.BitVec.extractLsb fraction 49 0) +++ 0b00#2)
                              (exp, fraction))
                            else
                              (let fraction : (BitVec 52) :=
                                ((Sail.BitVec.extractLsb fraction 50 0) +++ 0#1)
                              (exp, fraction))
                          (exp, fraction))
                        else (exp, fraction)
                      let exp : Int := exp
                      let scaled ← (( do
                        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at
                          (← occLabel 1090) 0 4095))) ) : SailM Nat )
                      let increasedprecision_name ← (( do
                        (pure ((← do
                              if ((((Sail.BitVec.length result) == 32) : Bool) : Bool)
                              then
                                (do
                                  (HaveFeatRPRES ()))
                              else (pure false)) && altfp)) ) : SailM Bool )
                      let scaled : Nat :=
                        if ((! increasedprecision_name) : Bool)
                        then (BitVec.toNat (1#1 +++ (Sail.BitVec.extractLsb fraction 51 44)))
                        else (BitVec.toNat (1#1 +++ (Sail.BitVec.extractLsb fraction 51 41)))
                      let scaled : Int := scaled
                      let result_exp ← (( do (undefined_int_at (← occLabel 1091) ()) ) : SailM
                        Int )
                      let result_exp : Int :=
                        match (Sail.BitVec.length result) with
                        | 16 => (29 -i exp)
                        | 32 => (253 -i exp)
                        | 64 => (2045 -i exp)
                        | _ => result_exp
                      let estimate ← (( do (RecipEstimate scaled increasedprecision_name) ) :
                        SailM Int )
                      let fraction : (BitVec 52) :=
                        if ((! increasedprecision_name) : Bool)
                        then ((integer_subrange estimate 7 0) +++ (Zeros (n := 44)))
                        else ((integer_subrange estimate 11 0) +++ (Zeros (n := 40)))
                      let (fraction, result_exp) : ((BitVec 52) × Int) :=
                        if ((result_exp == 0) : Bool)
                        then
                          (let fraction : (BitVec 52) :=
                            (1#1 +++ (Sail.BitVec.extractLsb fraction 51 1))
                          (fraction, result_exp))
                        else
                          (let (fraction, result_exp) : ((BitVec 52) × Int) :=
                            if ((result_exp == (Neg.neg 1)) : Bool)
                            then
                              (let fraction : (BitVec 52) :=
                                (0b01#2 +++ (Sail.BitVec.extractLsb fraction 51 2))
                              let result_exp : Int := 0
                              (fraction, result_exp))
                            else (fraction, result_exp)
                          (fraction, result_exp))
                      let result_exp : Int := result_exp
                      let result : (BitVec k_N) :=
                        match (Sail.BitVec.length result) with
                        | 16 =>
                          (Sail.BitVec.castWidth ((sign +++ (integer_subrange result_exp
                                ((Sail.BitVec.length result) -i 12) 0)) +++ (Sail.BitVec.extractLsb
                              fraction 51 42)))
                        | 32 =>
                          (Sail.BitVec.castWidth ((sign +++ (integer_subrange result_exp
                                ((Sail.BitVec.length result) -i 25) 0)) +++ (Sail.BitVec.extractLsb
                              fraction 51 29)))
                        | 64 =>
                          (Sail.BitVec.castWidth ((sign +++ (integer_subrange result_exp
                                ((Sail.BitVec.length result) -i 54) 0)) +++ (Sail.BitVec.extractLsb
                              fraction 51 0)))
                        | _ => result
                      (pure (result)))))))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPRecpX (op : (BitVec k_N)) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  let fptype ← (( do (undefined_FPType (← occLabel 1092) ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector_at (← occLabel 1093) 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real_at (← occLabel 1094) ()) ) : SailM real )
  ArmFull.assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length
          op) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:17407.41-17407.42"
  let fpcr : FPCRType := fpcr_in
  let esize : Int := 5
  let esize : Int :=
    match (Sail.BitVec.length op) with
    | 16 => 5
    | 32 => 8
    | 64 => 11
    | _ => esize
  let esize : Int := esize
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1095)
      (Sail.BitVec.length op))) ) : SailM (BitVec k_N) )
  let exp ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1096)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec (Sail.Int.toNatChecked (esize : Int))) )
  let frac : (BitVec (Sail.Int.toNatChecked ((k_N : Int) -i ((esize : Int) +i (1 : Int))))) :=
    (Sail.BitVec.castWidth (Zeros
      (n := (Sail.Int.toNatChecked (((Sail.BitVec.length result) -i (esize +i 1)))))))
  let altfp ← (( do
    (pure ((← do
          (HaveAltFP ())) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  let fpexc : Bool := (! altfp)
  let fpcr : (BitVec 64) :=
    if (altfp : Bool)
    then
      (let fpcr : FPCRType :=
        (Sail.BitVec.updateSubrange fpcr 0 0 (Sail.BitVec.extractLsb 0b11#2 1 1))
      (Sail.BitVec.updateSubrange fpcr 24 24 (Sail.BitVec.extractLsb 0b11#2 0 0)))
    else fpcr
  let w__1 ← (( do (FPUnpack__1 op fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let fptype : FPType := tup__0
  let sign : (BitVec 1) := tup__1
  let value_name : real := tup__2
  let exp ← (( do
    match (Sail.BitVec.length result) with
    | 16 =>
      (do
        ArmFull.assert ((10 ≤b ((10 +i esize) -i 1)) && (((10 +i esize) -i 1) <b (Sail.BitVec.length
              result))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:17434.75-17434.76"
        let exp : (BitVec (Sail.Int.toNatChecked (esize : Int))) :=
          (Sail.BitVec.castWidth (Sail.BitVec.extractLsb op
            (Sail.Int.toNatChecked (((10 +i esize) -i 1))) 10))
        (pure (exp)))
    | 32 =>
      (do
        ArmFull.assert ((23 ≤b ((23 +i esize) -i 1)) && (((23 +i esize) -i 1) <b (Sail.BitVec.length
              result))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:17438.75-17438.76"
        let exp : (BitVec (Sail.Int.toNatChecked (esize : Int))) :=
          (Sail.BitVec.castWidth (Sail.BitVec.extractLsb op
            (Sail.Int.toNatChecked (((23 +i esize) -i 1))) 23))
        (pure (exp)))
    | 64 =>
      (let exp : (BitVec (Sail.Int.toNatChecked (esize : Int))) :=
        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb op
          (Sail.Int.toNatChecked (((52 +i esize) -i 1))) 52))
      (pure (exp)))
    | _ => (pure (exp)) ) : SailM (BitVec (Sail.Int.toNatChecked (esize : Int))) )
  let max_exp : (BitVec (Sail.Int.toNatChecked (esize : Int))) :=
    (Sail.BitVec.castWidth (BitVec.subInt (Ones (n := (Sail.Int.toNatChecked (esize)))) 1))
  if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
  then
    (do
      (FPProcessNaN__1 fptype op fpcr fpexc))
  else
    (let result : (BitVec k_N) :=
      if ((IsZero exp) : Bool)
      then (Sail.BitVec.castWidth ((sign +++ max_exp) +++ frac))
      else (Sail.BitVec.castWidth ((sign +++ (Complement.complement exp)) +++ frac))
    (pure (result)))


/-- Type quantifiers: k_N : Nat, k_exact : Bool, List.elem k_N [16, 32, 64] -/
def FPRoundInt (op : (BitVec k_N)) (fpcr : (BitVec 64)) (rounding : FPRounding) (exact : Bool) : SailM (BitVec k_N) := do
  let error ← (( do (undefined_real_at (← occLabel 1097) ()) ) : SailM real )
  let fptype ← (( do (undefined_FPType (← occLabel 1098) ()) ) : SailM FPType )
  let int_result ← (( do (undefined_int_at (← occLabel 1099) ()) ) : SailM Int )
  let real_result ← (( do (undefined_real_at (← occLabel 1100) ()) ) : SailM real )
  let sign ← (( do (undefined_bitvector_at (← occLabel 1101) 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real_at (← occLabel 1102) ()) ) : SailM real )
  ArmFull.assert (bne rounding FPRounding_ODD) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:17470.37-17470.38"
  ArmFull.assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length
          op) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:17471.41-17471.42"
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
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1103)
      (Sail.BitVec.length op))) ) : SailM (BitVec k_N) )
  if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
  then
    (do
      (FPProcessNaN fptype op fpcr))
  else
    (do
      if ((BEq.beq fptype FPType_Infinity) : Bool)
      then
        (do
          ((Sail.BitVec.castWidth ) <$> (FPInfinity sign (Sail.BitVec.length result))))
      else
        (do
          if ((BEq.beq fptype FPType_Zero) : Bool)
          then
            (do
              ((Sail.BitVec.castWidth ) <$> (FPZero sign (Sail.BitVec.length result))))
          else
            (do
              let int_result : Int := (round_down value_name)
              let error : real := (sub_real value_name (to_real int_result))
              let round_up ← (( do (undefined_bool_at (← occLabel 1104) ()) ) : SailM Bool )
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
              let real_result : real := (to_real int_result)
              let result ← (( do
                if ((eq_real real_result (0)) : Bool)
                then
                  (do
                    ((Sail.BitVec.castWidth ) <$> (FPZero sign (Sail.BitVec.length result))))
                else
                  (do
                    ((Sail.BitVec.castWidth ) <$> (FPRound__1 real_result fpcr FPRounding_ZERO
                      (Sail.BitVec.length result)))) ) : SailM (BitVec k_N) )
              if (((bne error (0)) && exact) : Bool)
              then
                (do
                  (FPProcessException FPExc_Inexact fpcr))
              else (pure (()))
              (pure (result)))))


/-- Type quantifiers: k_N : Nat, intsize : Int, List.elem k_N [32, 64] -/
def FPRoundIntN (op : (BitVec k_N)) (fpcr : (BitVec 64)) (rounding : FPRounding) (intsize : Int) : SailM (BitVec k_N) := do
  let error ← (( do (undefined_real_at (← occLabel 1105) ()) ) : SailM real )
  let fptype ← (( do (undefined_FPType (← occLabel 1106) ()) ) : SailM FPType )
  let int_result ← (( do (undefined_int_at (← occLabel 1107) ()) ) : SailM Int )
  let overflow ← (( do (undefined_bool_at (← occLabel 1108) ()) ) : SailM Bool )
  let real_result ← (( do (undefined_real_at (← occLabel 1109) ()) ) : SailM real )
  let sign ← (( do (undefined_bitvector_at (← occLabel 1110) 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real_at (← occLabel 1111) ()) ) : SailM real )
  ArmFull.assert (bne rounding FPRounding_ODD) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:17533.37-17533.38"
  ArmFull.assert (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length op) == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:17534.30-17534.31"
  ArmFull.assert ((intsize == 32) || (intsize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:17535.40-17535.41"
  let exp ← (( do (undefined_int_at (← occLabel 1112) ()) ) : SailM Int )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1113)
      (Sail.BitVec.length op))) ) : SailM (BitVec k_N) )
  let round_up ← (( do (undefined_bool_at (← occLabel 1114) ()) ) : SailM Bool )
  let E : Nat :=
    if (((Sail.BitVec.length result) == 32) : Bool)
    then 8
    else 11
  let F : Int := ((Sail.BitVec.length result) -i (E +i 1))
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
  if (((BEq.beq fptype FPType_SNaN) || ((BEq.beq fptype FPType_QNaN) || (BEq.beq fptype
           FPType_Infinity))) : Bool)
  then
    (do
      let result : (BitVec k_N) :=
        if (((Sail.BitVec.length result) == 32) : Bool)
        then
          (let exp : Int := (126 +i intsize)
          (Sail.BitVec.castWidth ((1#1 +++ (integer_subrange exp (E -i 1) 0)) +++ (Zeros
              (n := (Sail.Int.toNatChecked (F)))))))
        else
          (let exp : Int := (1022 +i intsize)
          (Sail.BitVec.castWidth ((1#1 +++ (integer_subrange exp (E -i 1) 0)) +++ (Zeros
              (n := (Sail.Int.toNatChecked (F)))))))
      (FPProcessException FPExc_InvalidOp fpcr)
      (pure (result)))
  else
    (do
      if ((BEq.beq fptype FPType_Zero) : Bool)
      then
        (do
          ((Sail.BitVec.castWidth ) <$> (FPZero sign (Sail.BitVec.length result))))
      else
        (do
          let int_result : Int := (round_down value_name)
          let error : real := (sub_real value_name (to_real int_result))
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
          let overflow : Bool :=
            ((int_result >b ((2 ^i (intsize -i 1)) -i 1)) || (int_result <b ((Neg.neg 1) *i (2 ^i (intsize -i 1)))))
          let (error, result) ← (( do
            if (overflow : Bool)
            then
              (do
                let result : (BitVec k_N) :=
                  if (((Sail.BitVec.length result) == 32) : Bool)
                  then
                    (let exp : Int := (126 +i intsize)
                    (Sail.BitVec.castWidth ((1#1 +++ (integer_subrange exp (E -i 1) 0)) +++ (Zeros
                        (n := (Sail.Int.toNatChecked (F)))))))
                  else
                    (let exp : Int := (1022 +i intsize)
                    (Sail.BitVec.castWidth ((1#1 +++ (integer_subrange exp (E -i 1) 0)) +++ (Zeros
                        (n := (Sail.Int.toNatChecked (F)))))))
                (FPProcessException FPExc_InvalidOp fpcr)
                let error : real := (0)
                (pure ((error, result))))
            else
              (do
                let real_result : real := (to_real int_result)
                let result ← (( do
                  if ((eq_real real_result (0)) : Bool)
                  then
                    (do
                      ((Sail.BitVec.castWidth ) <$> (FPZero sign (Sail.BitVec.length result))))
                  else
                    (do
                      ((Sail.BitVec.castWidth ) <$> (FPRound__1 real_result fpcr FPRounding_ZERO
                        (Sail.BitVec.length result)))) ) : SailM (BitVec k_N) )
                (pure ((error, result)))) ) : SailM (real × (BitVec k_N)) )
          if ((bne error (0)) : Bool)
          then
            (do
              (FPProcessException FPExc_Inexact fpcr))
          else (pure (()))
          (pure (result))))


end ArmFull.Functions
