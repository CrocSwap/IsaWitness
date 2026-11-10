import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0015
import ArmFull.Fn.M0018
import ArmFull.Fn.M0087
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

/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPRound (op : real) (fpcr : (BitVec 64)) (N : Nat) : SailM (BitVec N) := do
  let w__0 ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  ((Sail.BitVec.castWidth ) <$> (FPRound__1 op fpcr w__0 N))


/-- Type quantifiers: k_M : Nat, N : Nat, fbits : Int, k_is_unsigned : Bool, List.elem N
  [16, 32, 64] ∧ List.elem k_M [16, 32, 64] -/
def FixedToFP (op : (BitVec k_M)) (fbits : Int) (is_unsigned : Bool) (fpcr : (BitVec 64)) (rounding : FPRounding) (N : Nat) : SailM (BitVec N) := do
  ArmFull.assert ((N == 16) || ((N == 32) || (N == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:15912.38-15912.39"
  ArmFull.assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length
          op) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:15913.41-15913.42"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 899)
      (Sail.Int.toNatChecked (N)))) ) : SailM (BitVec N) )
  ArmFull.assert (fbits ≥b 0) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:15915.21-15915.22"
  ArmFull.assert (bne rounding FPRounding_ODD) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:15916.37-15916.38"
  let int_operand ← (( do (asl_Int op is_unsigned) ) : SailM Int )
  let real_operand : real := (div_real (to_real int_operand) (real_power (2) fbits))
  if ((eq_real real_operand (0)) : Bool)
  then
    (do
      ((Sail.BitVec.castWidth ) <$> (FPZero 0#1 N)))
  else
    (do
      ((Sail.BitVec.castWidth ) <$> (FPRound__1 real_operand fpcr rounding N)))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPAbs (op : (BitVec k_N)) : SailM (BitVec k_N) := SailME.run do
  let fptype ← (( do (undefined_FPType (← occLabel 918) ()) ) : SailME (BitVec k_N) FPType )
  ArmFull.assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length
          op) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:16099.41-16099.42"
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
  (pure ((Sail.BitVec.castWidth (0#1 +++ (Sail.BitVec.extractLsb op
        (Sail.Int.toNatChecked (((Sail.BitVec.length op) -i 2))) 0)))))


/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, List.elem k_N [16, 32, 64] -/
def FPAdd__1 (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (BitVec k_N) := do
  let done ← (( do (undefined_bool_at (← occLabel 921) ()) ) : SailM Bool )
  let inf1 ← (( do (undefined_bool_at (← occLabel 922) ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool_at (← occLabel 923) ()) ) : SailM Bool )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 924)
      (Sail.BitVec.length op2))) ) : SailM (BitVec k_N) )
  let result_sign ← (( do (undefined_bitvector_at (← occLabel 925) 1) ) : SailM (BitVec 1) )
  let result_value ← (( do (undefined_real_at (← occLabel 926) ()) ) : SailM real )
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 927) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 928) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 929) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 930) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 931) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 932) ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool_at (← occLabel 933) ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool_at (← occLabel 934) ()) ) : SailM Bool )
  ArmFull.assert (((Sail.BitVec.length result) == 16) || (((Sail.BitVec.length result) == 32) || ((Sail.BitVec.length
          result) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:16263.41-16263.42"
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
        if (((inf1 && inf2) && (sign1 == (Complement.complement sign2))) : Bool)
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
            if (((inf1 && (sign1 == 0#1)) || (inf2 && (sign2 == 0#1))) : Bool)
            then
              (do
                ((Sail.BitVec.castWidth ) <$> (FPInfinity 0#1 (Sail.BitVec.length result))))
            else
              (do
                if (((inf1 && (sign1 == 1#1)) || (inf2 && (sign2 == 1#1))) : Bool)
                then
                  (do
                    ((Sail.BitVec.castWidth ) <$> (FPInfinity 1#1 (Sail.BitVec.length result))))
                else
                  (do
                    if (((zero1 && zero2) && (sign1 == sign2)) : Bool)
                    then
                      (do
                        ((Sail.BitVec.castWidth ) <$> (FPZero sign1 (Sail.BitVec.length result))))
                    else
                      (do
                        let result_value : real := (add_real value1_name value2_name)
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


/-- Type quantifiers: k_N : Nat, k_signal_nans : Bool, List.elem k_N [16, 32, 64] -/
def FPCompare (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (signal_nans : Bool) (fpcr : (BitVec 64)) : SailM (BitVec 4) := do
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 935) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 936) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 937) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 938) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 939) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 940) ()) ) : SailM real )
  ArmFull.assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length
          op2) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:16326.41-16326.42"
  let w__0 ← (( do (FPUnpack op1 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let type1 : FPType := tup__0
  let sign1 : (BitVec 1) := tup__1
  let value1_name : real := tup__2
  let w__1 ← (( do (FPUnpack op2 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let type2 : FPType := tup__0
  let sign2 : (BitVec 1) := tup__1
  let value2_name : real := tup__2
  let result ← (( do (undefined_bitvector_at (← occLabel 941) 4) ) : SailM (BitVec 4) )
  if ((((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN)) || ((BEq.beq type2 FPType_SNaN) || (BEq.beq
           type2 FPType_QNaN))) : Bool)
  then
    (do
      let result : (BitVec 4) := 0b0011#4
      if ((((BEq.beq type1 FPType_SNaN) || (BEq.beq type2 FPType_SNaN)) || signal_nans) : Bool)
      then
        (do
          (FPProcessException FPExc_InvalidOp fpcr))
      else (pure (()))
      (pure (result)))
  else
    (do
      let result : (BitVec 4) :=
        if ((eq_real value1_name value2_name) : Bool)
        then 0b0110#4
        else
          (if ((lt_real value1_name value2_name) : Bool)
          then 0b1000#4
          else 0b0010#4)
      (FPProcessDenorms type1 type2 (Sail.BitVec.length op2) fpcr)
      (pure (result)))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPCompareEQ (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM Bool := do
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 942) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 943) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 944) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 945) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 946) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 947) ()) ) : SailM real )
  ArmFull.assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length
          op2) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:16359.41-16359.42"
  let w__0 ← (( do (FPUnpack op1 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let type1 : FPType := tup__0
  let sign1 : (BitVec 1) := tup__1
  let value1_name : real := tup__2
  let w__1 ← (( do (FPUnpack op2 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let type2 : FPType := tup__0
  let sign2 : (BitVec 1) := tup__1
  let value2_name : real := tup__2
  let result ← (( do (undefined_bool_at (← occLabel 948) ()) ) : SailM Bool )
  if ((((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN)) || ((BEq.beq type2 FPType_SNaN) || (BEq.beq
           type2 FPType_QNaN))) : Bool)
  then
    (do
      let result : Bool := false
      if (((BEq.beq type1 FPType_SNaN) || (BEq.beq type2 FPType_SNaN)) : Bool)
      then
        (do
          (FPProcessException FPExc_InvalidOp fpcr))
      else (pure (()))
      (pure (result)))
  else
    (do
      let result : Bool := (eq_real value1_name value2_name)
      (FPProcessDenorms type1 type2 (Sail.BitVec.length op2) fpcr)
      (pure (result)))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPCompareGE (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM Bool := do
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 949) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 950) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 951) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 952) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 953) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 954) ()) ) : SailM real )
  ArmFull.assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length
          op2) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:16386.41-16386.42"
  let w__0 ← (( do (FPUnpack op1 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let type1 : FPType := tup__0
  let sign1 : (BitVec 1) := tup__1
  let value1_name : real := tup__2
  let w__1 ← (( do (FPUnpack op2 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let type2 : FPType := tup__0
  let sign2 : (BitVec 1) := tup__1
  let value2_name : real := tup__2
  let result ← (( do (undefined_bool_at (← occLabel 955) ()) ) : SailM Bool )
  if ((((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN)) || ((BEq.beq type2 FPType_SNaN) || (BEq.beq
           type2 FPType_QNaN))) : Bool)
  then
    (do
      let result : Bool := false
      (FPProcessException FPExc_InvalidOp fpcr)
      (pure (result)))
  else
    (do
      let result : Bool := (gteq_real value1_name value2_name)
      (FPProcessDenorms type1 type2 (Sail.BitVec.length op2) fpcr)
      (pure (result)))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPCompareGT (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM Bool := do
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 956) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 957) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 958) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 959) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 960) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 961) ()) ) : SailM real )
  ArmFull.assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length
          op2) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:16410.41-16410.42"
  let w__0 ← (( do (FPUnpack op1 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let type1 : FPType := tup__0
  let sign1 : (BitVec 1) := tup__1
  let value1_name : real := tup__2
  let w__1 ← (( do (FPUnpack op2 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let type2 : FPType := tup__0
  let sign2 : (BitVec 1) := tup__1
  let value2_name : real := tup__2
  let result ← (( do (undefined_bool_at (← occLabel 962) ()) ) : SailM Bool )
  if ((((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN)) || ((BEq.beq type2 FPType_SNaN) || (BEq.beq
           type2 FPType_QNaN))) : Bool)
  then
    (do
      let result : Bool := false
      (FPProcessException FPExc_InvalidOp fpcr)
      (pure (result)))
  else
    (do
      let result : Bool := (gt_real value1_name value2_name)
      (FPProcessDenorms type1 type2 (Sail.BitVec.length op2) fpcr)
      (pure (result)))


/-- Type quantifiers: M : Nat, k_N : Nat, List.elem M [16, 32, 64] ∧ List.elem k_N [16, 32, 64] -/
def FPConvert (op : (BitVec k_N)) (fpcr : (BitVec 64)) (rounding : FPRounding) (M : Nat) : SailM (BitVec M) := do
  let fptype ← (( do (undefined_FPType (← occLabel 968) ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector_at (← occLabel 969) 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real_at (← occLabel 970) ()) ) : SailM real )
  ArmFull.assert ((M == 16) || ((M == 32) || (M == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:16508.38-16508.39"
  ArmFull.assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length
          op) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:16509.41-16509.42"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 971)
      (Sail.Int.toNatChecked (M)))) ) : SailM (BitVec M) )
  let w__0 ← (( do (FPUnpackCV op fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let fptype : FPType := tup__0
  let sign : (BitVec 1) := tup__1
  let value_name : real := tup__2
  let alt_hp : Bool := ((M == 16) && ((_get_FPCRType_AHP fpcr) == 1#1))
  if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
  then
    (do
      let result ← (( do
        if (alt_hp : Bool)
        then
          (do
            ((Sail.BitVec.castWidth ) <$> (FPZero sign M)))
        else
          (do
            if (((_get_FPCRType_DN fpcr) == 1#1) : Bool)
            then
              (do
                ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN__1 fpcr M)))
            else
              (do
                ((Sail.BitVec.castWidth ) <$> (FPConvertNaN op M)))) ) : SailM (BitVec M) )
      if (((BEq.beq fptype FPType_SNaN) || alt_hp) : Bool)
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
          if (alt_hp : Bool)
          then
            (do
              let result : (BitVec M) :=
                (Sail.BitVec.castWidth (sign +++ (Ones (n := (Sail.Int.toNatChecked ((M -i 1)))))))
              (FPProcessException FPExc_InvalidOp fpcr)
              (pure (result)))
          else
            (do
              ((Sail.BitVec.castWidth ) <$> (FPInfinity sign M))))
      else
        (do
          if ((BEq.beq fptype FPType_Zero) : Bool)
          then
            (do
              ((Sail.BitVec.castWidth ) <$> (FPZero sign M)))
          else
            (do
              let w__6 ← (( do
                ((Sail.BitVec.castWidth ) <$> (FPRoundCV value_name fpcr rounding M)) ) : SailM
                (BitVec M) )
              let result := (w__6 : (BitVec M))
              (FPProcessDenorm fptype (Sail.BitVec.length op) fpcr)
              (pure (result)))))


/-- Type quantifiers: k_N : Nat, k_altfp : Bool, List.elem k_N [16, 32, 64] -/
def FPMax__1 (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr_in : (BitVec 64)) (altfp : Bool) : SailM (BitVec k_N) := do
  let rounding ← (( do (undefined_FPRounding (← occLabel 985) ()) ) : SailM FPRounding )
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 986) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 987) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 988) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 989) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 990) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 991) ()) ) : SailM real )
  ArmFull.assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length
          op2) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:16634.41-16634.42"
  let done ← (( do (undefined_bool_at (← occLabel 992) ()) ) : SailM Bool )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 993)
      (Sail.BitVec.length op2))) ) : SailM (BitVec k_N) )
  let fpcr : FPCRType := fpcr_in
  let w__0 ← (( do (FPUnpack op1 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let type1 : FPType := tup__0
  let sign1 : (BitVec 1) := tup__1
  let value1_name : real := tup__2
  let w__1 ← (( do (FPUnpack op2 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let type2 : FPType := tup__0
  let sign2 : (BitVec 1) := tup__1
  let value2_name : real := tup__2
  if ((((altfp && (BEq.beq type1 FPType_Zero)) && (BEq.beq type2 FPType_Zero)) && (sign1 != sign2)) : Bool)
  then
    (do
      ((Sail.BitVec.castWidth ) <$> (FPZero sign2 (Sail.BitVec.length result))))
  else
    (do
      if ((altfp && (((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN)) || ((BEq.beq type2
                 FPType_SNaN) || (BEq.beq type2 FPType_QNaN)))) : Bool)
      then
        (do
          (FPProcessException FPExc_InvalidOp fpcr)
          if ((BEq.beq type2 FPType_Zero) : Bool)
          then
            (do
              ((Sail.BitVec.castWidth ) <$> (FPZero sign2 (Sail.BitVec.length result))))
          else (pure (op2)))
      else
        (do
          let w__5 ← (( do (FPProcessNaNs type1 type2 op1 op2 fpcr) ) : SailM
            (Bool × (BitVec k_N)) )
          let (tup__0, tup__1) := (w__5 : (Bool × (BitVec k_N)))
          let done : Bool := tup__0
          let result : (BitVec k_N) := tup__1
          if ((! done) : Bool)
          then
            (do
              let fptype ← (( do (undefined_FPType (← occLabel 994) ()) ) : SailM FPType )
              let sign ← (( do (undefined_bitvector_at (← occLabel 995) 1) ) : SailM (BitVec 1)
                )
              let value_name ← (( do (undefined_real_at (← occLabel 996) ()) ) : SailM real )
              let (fptype, sign, value_name) : (FPType × (BitVec 1) × real) :=
                if ((gt_real value1_name value2_name) : Bool)
                then
                  (let (tup__0, tup__1, tup__2) :=
                    ((type1, sign1, value1_name) : (FPType × (BitVec 1) × real))
                  let fptype : FPType := tup__0
                  let sign : (BitVec 1) := tup__1
                  let value_name : real := tup__2
                  (fptype, sign, value_name))
                else
                  (let (tup__0, tup__1, tup__2) :=
                    ((type2, sign2, value2_name) : (FPType × (BitVec 1) × real))
                  let fptype : FPType := tup__0
                  let sign : (BitVec 1) := tup__1
                  let value_name : real := tup__2
                  (fptype, sign, value_name))
              let (fpcr, result) ← (( do
                if ((BEq.beq fptype FPType_Infinity) : Bool)
                then
                  (do
                    let w__6 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (FPInfinity sign (Sail.BitVec.length result))) )
                      : SailM (BitVec k_N) )
                    let result := (w__6 : (BitVec k_N))
                    (pure ((fpcr, result))))
                else
                  (do
                    if ((BEq.beq fptype FPType_Zero) : Bool)
                    then
                      (do
                        let sign : (BitVec 1) := (sign1 &&& sign2)
                        let w__7 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (FPZero sign (Sail.BitVec.length result))) )
                          : SailM (BitVec k_N) )
                        let result := (w__7 : (BitVec k_N))
                        (pure ((fpcr, result))))
                    else
                      (do
                        let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
                        let fpcr : (BitVec 64) :=
                          if (altfp : Bool)
                          then
                            (let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 24 24 0#1)
                            (Sail.BitVec.updateSubrange fpcr 19 19 0#1))
                          else fpcr
                        let w__8 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (FPRound__2 value_name fpcr rounding true
                            (Sail.BitVec.length result))) ) : SailM (BitVec k_N) )
                        let result := (w__8 : (BitVec k_N))
                        (pure ((fpcr, result))))) ) : SailM ((BitVec 64) × (BitVec k_N)) )
              (FPProcessDenorms type1 type2 (Sail.BitVec.length result) fpcr)
              (pure (result)))
          else (pure (result))))


/-- Type quantifiers: k_N : Nat, k_altfp : Bool, List.elem k_N [16, 32, 64] -/
def FPMin__1 (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr_in : (BitVec 64)) (altfp : Bool) : SailM (BitVec k_N) := do
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 999) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 1000) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 1001) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 1002) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 1003) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 1004) ()) ) : SailM real )
  ArmFull.assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length
          op2) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:16735.41-16735.42"
  let done ← (( do (undefined_bool_at (← occLabel 1005) ()) ) : SailM Bool )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1006)
      (Sail.BitVec.length op2))) ) : SailM (BitVec k_N) )
  let fpcr : FPCRType := fpcr_in
  let w__0 ← (( do (FPUnpack op1 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let type1 : FPType := tup__0
  let sign1 : (BitVec 1) := tup__1
  let value1_name : real := tup__2
  let w__1 ← (( do (FPUnpack op2 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let type2 : FPType := tup__0
  let sign2 : (BitVec 1) := tup__1
  let value2_name : real := tup__2
  if ((((altfp && (BEq.beq type1 FPType_Zero)) && (BEq.beq type2 FPType_Zero)) && (sign1 != sign2)) : Bool)
  then
    (do
      ((Sail.BitVec.castWidth ) <$> (FPZero sign2 (Sail.BitVec.length result))))
  else
    (do
      if ((altfp && (((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN)) || ((BEq.beq type2
                 FPType_SNaN) || (BEq.beq type2 FPType_QNaN)))) : Bool)
      then
        (do
          (FPProcessException FPExc_InvalidOp fpcr)
          if ((BEq.beq type2 FPType_Zero) : Bool)
          then
            (do
              ((Sail.BitVec.castWidth ) <$> (FPZero sign2 (Sail.BitVec.length result))))
          else (pure (op2)))
      else
        (do
          let w__5 ← (( do (FPProcessNaNs type1 type2 op1 op2 fpcr) ) : SailM
            (Bool × (BitVec k_N)) )
          let (tup__0, tup__1) := (w__5 : (Bool × (BitVec k_N)))
          let done : Bool := tup__0
          let result : (BitVec k_N) := tup__1
          if ((! done) : Bool)
          then
            (do
              let fptype ← (( do (undefined_FPType (← occLabel 1007) ()) ) : SailM FPType )
              let sign ← (( do (undefined_bitvector_at (← occLabel 1008) 1) ) : SailM (BitVec 1)
                )
              let value_name ← (( do (undefined_real_at (← occLabel 1009) ()) ) : SailM real )
              let rounding ← (( do (undefined_FPRounding (← occLabel 1010) ()) ) : SailM
                FPRounding )
              let (fptype, sign, value_name) : (FPType × (BitVec 1) × real) :=
                if ((lt_real value1_name value2_name) : Bool)
                then
                  (let (tup__0, tup__1, tup__2) :=
                    ((type1, sign1, value1_name) : (FPType × (BitVec 1) × real))
                  let fptype : FPType := tup__0
                  let sign : (BitVec 1) := tup__1
                  let value_name : real := tup__2
                  (fptype, sign, value_name))
                else
                  (let (tup__0, tup__1, tup__2) :=
                    ((type2, sign2, value2_name) : (FPType × (BitVec 1) × real))
                  let fptype : FPType := tup__0
                  let sign : (BitVec 1) := tup__1
                  let value_name : real := tup__2
                  (fptype, sign, value_name))
              let (fpcr, result) ← (( do
                if ((BEq.beq fptype FPType_Infinity) : Bool)
                then
                  (do
                    let w__6 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (FPInfinity sign (Sail.BitVec.length result))) )
                      : SailM (BitVec k_N) )
                    let result := (w__6 : (BitVec k_N))
                    (pure ((fpcr, result))))
                else
                  (do
                    if ((BEq.beq fptype FPType_Zero) : Bool)
                    then
                      (do
                        let sign : (BitVec 1) := (sign1 ||| sign2)
                        let w__7 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (FPZero sign (Sail.BitVec.length result))) )
                          : SailM (BitVec k_N) )
                        let result := (w__7 : (BitVec k_N))
                        (pure ((fpcr, result))))
                    else
                      (do
                        let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
                        let fpcr : (BitVec 64) :=
                          if (altfp : Bool)
                          then
                            (let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 24 24 0#1)
                            (Sail.BitVec.updateSubrange fpcr 19 19 0#1))
                          else fpcr
                        let w__8 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (FPRound__2 value_name fpcr rounding true
                            (Sail.BitVec.length result))) ) : SailM (BitVec k_N) )
                        let result := (w__8 : (BitVec k_N))
                        (pure ((fpcr, result))))) ) : SailM ((BitVec 64) × (BitVec k_N)) )
              (FPProcessDenorms type1 type2 (Sail.BitVec.length result) fpcr)
              (pure (result)))
          else (pure (result))))


/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, List.elem k_N [16, 32, 64] -/
def FPMulAdd__1 (addend : (BitVec k_N)) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (BitVec k_N) := do
  let done ← (( do (undefined_bool_at (← occLabel 1028) ()) ) : SailM Bool )
  let infA ← (( do (undefined_bool_at (← occLabel 1029) ()) ) : SailM Bool )
  let infP ← (( do (undefined_bool_at (← occLabel 1030) ()) ) : SailM Bool )
  let invalidop ← (( do (undefined_bool_at (← occLabel 1031) ()) ) : SailM Bool )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1032)
      (Sail.BitVec.length op2))) ) : SailM (BitVec k_N) )
  let result_sign ← (( do (undefined_bitvector_at (← occLabel 1033) 1) ) : SailM (BitVec 1) )
  let result_value ← (( do (undefined_real_at (← occLabel 1034) ()) ) : SailM real )
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 1035) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 1036) 1) ) : SailM (BitVec 1) )
  let signA ← (( do (undefined_bitvector_at (← occLabel 1037) 1) ) : SailM (BitVec 1) )
  let signP ← (( do (undefined_bitvector_at (← occLabel 1038) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 1039) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 1040) ()) ) : SailM FPType )
  let typeA ← (( do (undefined_FPType (← occLabel 1041) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 1042) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 1043) ()) ) : SailM real )
  let valueA_name ← (( do (undefined_real_at (← occLabel 1044) ()) ) : SailM real )
  let zeroA ← (( do (undefined_bool_at (← occLabel 1045) ()) ) : SailM Bool )
  let zeroP ← (( do (undefined_bool_at (← occLabel 1046) ()) ) : SailM Bool )
  ArmFull.assert (((Sail.BitVec.length result) == 16) || (((Sail.BitVec.length result) == 32) || ((Sail.BitVec.length
          result) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:16945.41-16945.42"
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
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
  let zero1 : Bool := (BEq.beq type1 FPType_Zero)
  let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
  let zero2 : Bool := (BEq.beq type2 FPType_Zero)
  let w__3 ← (( do (FPProcessNaNs3__1 typeA type1 type2 addend op1 op2 fpcr fpexc) ) : SailM
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
          (FPProcessDenorms3 typeA type1 type2 (Sail.BitVec.length result) fpcr))
      else (pure (()))
      (pure (result)))
  else (pure (result))


end ArmFull.Functions
