import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0015
import ArmFull.Fn.M0018
import ArmFull.Fn.M0116
import ArmFull.Fn.M0121
import ArmFull.Fn.M0145
import ArmFull.Fn.M0153
import ArmFull.Fn.M0167
import ArmFull.Fn.M0840
import ArmFull.Fn.M0852
import ArmFull.Fn.M0923
import ArmFull.Fn.M0924
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

/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, k_N = 16 -/
def BFSub__1 (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (BitVec k_N) := do
  let inf1 ← (( do (undefined_bool_at (← occLabel 1843) ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool_at (← occLabel 1844) ()) ) : SailM Bool )
  let result_sign ← (( do (undefined_bitvector_at (← occLabel 1845) 1) ) : SailM (BitVec 1) )
  let result_value ← (( do (undefined_real_at (← occLabel 1846) ()) ) : SailM real )
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 1847) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 1848) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 1849) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 1850) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 1851) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 1852) ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool_at (← occLabel 1853) ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool_at (← occLabel 1854) ()) ) : SailM Bool )
  ArmFull.assert ((Sail.BitVec.length op2) == 16) "sail-arm/v8_base.sail:32590.19-32590.20"
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let done ← (( do (undefined_bool_at (← occLabel 1855) ()) ) : SailM Bool )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1856)
      (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))) ) : SailM (BitVec (2 * k_N)) )
  let op1_s : (BitVec (2 * k_N)) :=
    (Sail.BitVec.castWidth (op1 +++ (Zeros (n := (Sail.BitVec.length op2)))))
  let op2_s : (BitVec (2 * k_N)) :=
    (Sail.BitVec.castWidth (op2 +++ (Zeros (n := (Sail.BitVec.length op2)))))
  let w__0 ← (( do (FPUnpack__1 op1_s fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let type1 : FPType := tup__0
  let sign1 : (BitVec 1) := tup__1
  let value1_name : real := tup__2
  let w__1 ← (( do (FPUnpack__1 op2_s fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let type2 : FPType := tup__0
  let sign2 : (BitVec 1) := tup__1
  let value2_name : real := tup__2
  let w__2 ← (( do (FPProcessNaNs__1 type1 type2 op1_s op2_s fpcr fpexc) ) : SailM
    (Bool × (BitVec (2 * k_N))) )
  let (tup__0, tup__1) := (w__2 : (Bool × (BitVec (2 * k_N))))
  let done : Bool := tup__0
  let result : (BitVec (2 * k_N)) := tup__1
  let result ← (( do
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
                ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN__1 fpcr
                  (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))) ) : SailM
                (BitVec (2 * k_N)) )
              let result := (w__3 : (BitVec (2 * k_N)))
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
                  ((Sail.BitVec.castWidth ) <$> (FPInfinity 0#1
                    (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))))
              else
                (do
                  if (((inf1 && (sign1 == 1#1)) || (inf2 && (sign2 == 0#1))) : Bool)
                  then
                    (do
                      ((Sail.BitVec.castWidth ) <$> (FPInfinity 1#1
                        (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))))
                  else
                    (do
                      if (((zero1 && zero2) && (sign1 == (Complement.complement sign2))) : Bool)
                      then
                        (do
                          ((Sail.BitVec.castWidth ) <$> (FPZero sign1
                            (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))))
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
                                (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))))
                          else
                            (do
                              ((Sail.BitVec.castWidth ) <$> (FPRoundBF result_value fpcr rounding
                                fpexc (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))))))))
          ) : SailM (BitVec (2 * k_N)) )
        if (fpexc : Bool)
        then
          (do
            (FPProcessDenorms type1 type2 (2 *i (Sail.BitVec.length op2)) fpcr))
        else (pure (()))
        (pure (result)))
    else (pure (result)) ) : SailM (BitVec (2 * k_N)) )
  (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb result
      (Sail.Int.toNatChecked (((2 *i (Sail.BitVec.length op2)) -i 1))) (Sail.BitVec.length op2)))))


/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, k_N = 16 -/
def BFMulAdd__1 (addend : (BitVec k_N)) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (BitVec k_N) := do
  let infA ← (( do (undefined_bool_at (← occLabel 1857) ()) ) : SailM Bool )
  let infP ← (( do (undefined_bool_at (← occLabel 1858) ()) ) : SailM Bool )
  let invalidop ← (( do (undefined_bool_at (← occLabel 1859) ()) ) : SailM Bool )
  let result_sign ← (( do (undefined_bitvector_at (← occLabel 1860) 1) ) : SailM (BitVec 1) )
  let result_value ← (( do (undefined_real_at (← occLabel 1861) ()) ) : SailM real )
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 1862) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 1863) 1) ) : SailM (BitVec 1) )
  let signA ← (( do (undefined_bitvector_at (← occLabel 1864) 1) ) : SailM (BitVec 1) )
  let signP ← (( do (undefined_bitvector_at (← occLabel 1865) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 1866) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 1867) ()) ) : SailM FPType )
  let typeA ← (( do (undefined_FPType (← occLabel 1868) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 1869) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 1870) ()) ) : SailM real )
  let valueA_name ← (( do (undefined_real_at (← occLabel 1871) ()) ) : SailM real )
  let zeroA ← (( do (undefined_bool_at (← occLabel 1872) ()) ) : SailM Bool )
  let zeroP ← (( do (undefined_bool_at (← occLabel 1873) ()) ) : SailM Bool )
  ArmFull.assert ((Sail.BitVec.length op2) == 16) "sail-arm/v8_base.sail:32674.19-32674.20"
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let done ← (( do (undefined_bool_at (← occLabel 1874) ()) ) : SailM Bool )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1875)
      (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))) ) : SailM (BitVec (2 * k_N)) )
  let addend_s : (BitVec (2 * k_N)) :=
    (Sail.BitVec.castWidth (addend +++ (Zeros (n := (Sail.BitVec.length op2)))))
  let op1_s : (BitVec (2 * k_N)) :=
    (Sail.BitVec.castWidth (op1 +++ (Zeros (n := (Sail.BitVec.length op2)))))
  let op2_s : (BitVec (2 * k_N)) :=
    (Sail.BitVec.castWidth (op2 +++ (Zeros (n := (Sail.BitVec.length op2)))))
  let w__0 ← (( do (FPUnpack__1 addend_s fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let typeA : FPType := tup__0
  let signA : (BitVec 1) := tup__1
  let valueA_name : real := tup__2
  let w__1 ← (( do (FPUnpack__1 op1_s fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let type1 : FPType := tup__0
  let sign1 : (BitVec 1) := tup__1
  let value1_name : real := tup__2
  let w__2 ← (( do (FPUnpack__1 op2_s fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__2 : (FPType × (BitVec 1) × real))
  let type2 : FPType := tup__0
  let sign2 : (BitVec 1) := tup__1
  let value2_name : real := tup__2
  let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
  let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
  let zero1 : Bool := (BEq.beq type1 FPType_Zero)
  let zero2 : Bool := (BEq.beq type2 FPType_Zero)
  let w__3 ← (( do (FPProcessNaNs3__1 typeA type1 type2 addend_s op1_s op2_s fpcr fpexc) ) : SailM
    (Bool × (BitVec (2 * k_N))) )
  let (tup__0, tup__1) := (w__3 : (Bool × (BitVec (2 * k_N))))
  let done : Bool := tup__0
  let result : (BitVec (2 * k_N)) := tup__1
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
              ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN__1 fpcr
                (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))) ) : SailM
              (BitVec (2 * k_N)) )
            let result := (w__8 : (BitVec (2 * k_N)))
            if (fpexc : Bool)
            then
              (do
                (FPProcessException FPExc_InvalidOp fpcr))
            else (pure (()))
            (pure (result)))
        else (pure (result)))
    else (pure (result)) ) : SailM (BitVec (2 * k_N)) )
  let result ← (( do
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
                ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN__1 fpcr
                  (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))) ) : SailM
                (BitVec (2 * k_N)) )
              let result := (w__9 : (BitVec (2 * k_N)))
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
                  ((Sail.BitVec.castWidth ) <$> (FPInfinity 0#1
                    (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))))
              else
                (do
                  if (((infA && (signA == 1#1)) || (infP && (signP == 1#1))) : Bool)
                  then
                    (do
                      ((Sail.BitVec.castWidth ) <$> (FPInfinity 1#1
                        (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))))
                  else
                    (do
                      if (((zeroA && zeroP) && (signA == signP)) : Bool)
                      then
                        (do
                          ((Sail.BitVec.castWidth ) <$> (FPZero signA
                            (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))))
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
                                (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))))
                          else
                            (do
                              ((Sail.BitVec.castWidth ) <$> (FPRoundBF result_value fpcr rounding
                                fpexc (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))))))))
          ) : SailM (BitVec (2 * k_N)) )
        if (((! invalidop) && fpexc) : Bool)
        then
          (do
            (FPProcessDenorms3 typeA type1 type2 (2 *i (Sail.BitVec.length op2)) fpcr))
        else (pure (()))
        (pure (result)))
    else (pure (result)) ) : SailM (BitVec (2 * k_N)) )
  (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb result
      (Sail.Int.toNatChecked (((2 *i (Sail.BitVec.length op2)) -i 1))) (Sail.BitVec.length op2)))))


/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, k_N = 16 -/
def BFMul__1 (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (BitVec k_N) := do
  let inf1 ← (( do (undefined_bool_at (← occLabel 1876) ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool_at (← occLabel 1877) ()) ) : SailM Bool )
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 1878) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 1879) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 1880) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 1881) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 1882) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 1883) ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool_at (← occLabel 1884) ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool_at (← occLabel 1885) ()) ) : SailM Bool )
  ArmFull.assert ((Sail.BitVec.length op2) == 16) "sail-arm/v8_base.sail:32769.19-32769.20"
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let done ← (( do (undefined_bool_at (← occLabel 1886) ()) ) : SailM Bool )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1887)
      (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))) ) : SailM (BitVec (2 * k_N)) )
  let op1_s : (BitVec (2 * k_N)) :=
    (Sail.BitVec.castWidth (op1 +++ (Zeros (n := (Sail.BitVec.length op2)))))
  let op2_s : (BitVec (2 * k_N)) :=
    (Sail.BitVec.castWidth (op2 +++ (Zeros (n := (Sail.BitVec.length op2)))))
  let w__0 ← (( do (FPUnpack__1 op1_s fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let type1 : FPType := tup__0
  let sign1 : (BitVec 1) := tup__1
  let value1_name : real := tup__2
  let w__1 ← (( do (FPUnpack__1 op2_s fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let type2 : FPType := tup__0
  let sign2 : (BitVec 1) := tup__1
  let value2_name : real := tup__2
  let w__2 ← (( do (FPProcessNaNs__1 type1 type2 op1_s op2_s fpcr fpexc) ) : SailM
    (Bool × (BitVec (2 * k_N))) )
  let (tup__0, tup__1) := (w__2 : (Bool × (BitVec (2 * k_N))))
  let done : Bool := tup__0
  let result : (BitVec (2 * k_N)) := tup__1
  let result ← (( do
    if ((! done) : Bool)
    then
      (do
        let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
        let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
        let zero1 : Bool := (BEq.beq type1 FPType_Zero)
        let zero2 : Bool := (BEq.beq type2 FPType_Zero)
        let result ← (( do
          if (((inf1 && zero2) || (zero1 && inf2)) : Bool)
          then
            (do
              let w__3 ← (( do
                ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN__1 fpcr
                  (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))) ) : SailM
                (BitVec (2 * k_N)) )
              let result := (w__3 : (BitVec (2 * k_N)))
              if (fpexc : Bool)
              then
                (do
                  (FPProcessException FPExc_InvalidOp fpcr))
              else (pure (()))
              (pure (result)))
          else
            (do
              if ((inf1 || inf2) : Bool)
              then
                (do
                  ((Sail.BitVec.castWidth ) <$> (FPInfinity (sign1 ^^^ sign2)
                    (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))))
              else
                (do
                  if ((zero1 || zero2) : Bool)
                  then
                    (do
                      ((Sail.BitVec.castWidth ) <$> (FPZero (sign1 ^^^ sign2)
                        (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))))
                  else
                    (do
                      ((Sail.BitVec.castWidth ) <$> (FPRoundBF (mult_real value1_name value2_name)
                        fpcr rounding fpexc
                        (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2))))))))) ) : SailM
          (BitVec (2 * k_N)) )
        if (fpexc : Bool)
        then
          (do
            (FPProcessDenorms type1 type2 (2 *i (Sail.BitVec.length op2)) fpcr))
        else (pure (()))
        (pure (result)))
    else (pure (result)) ) : SailM (BitVec (2 * k_N)) )
  (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb result
      (Sail.Int.toNatChecked (((2 *i (Sail.BitVec.length op2)) -i 1))) (Sail.BitVec.length op2)))))


/-- Type quantifiers: k_N : Nat, k_altfp : Bool, k_N = 16 -/
def BFMin__1 (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr_in : (BitVec 64)) (altfp : Bool) : SailM (BitVec k_N) := do
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 1888) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 1889) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 1890) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 1891) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 1892) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 1893) ()) ) : SailM real )
  ArmFull.assert ((Sail.BitVec.length op2) == 16) "sail-arm/v8_base.sail:32821.19-32821.20"
  let fpcr : FPCRType := fpcr_in
  let fpexc : Bool := true
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let done ← (( do (undefined_bool_at (← occLabel 1894) ()) ) : SailM Bool )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1895)
      (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))) ) : SailM (BitVec (2 * k_N)) )
  let op1_s : (BitVec (2 * k_N)) :=
    (Sail.BitVec.castWidth (op1 +++ (Zeros (n := (Sail.BitVec.length op2)))))
  let op2_s : (BitVec (2 * k_N)) :=
    (Sail.BitVec.castWidth (op2 +++ (Zeros (n := (Sail.BitVec.length op2)))))
  let w__0 ← (( do (FPUnpack__1 op1_s fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let type1 : FPType := tup__0
  let sign1 : (BitVec 1) := tup__1
  let value1_name : real := tup__2
  let w__1 ← (( do (FPUnpack__1 op2_s fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let type2 : FPType := tup__0
  let sign2 : (BitVec 1) := tup__1
  let value2_name : real := tup__2
  if ((((altfp && (BEq.beq type1 FPType_Zero)) && (BEq.beq type2 FPType_Zero)) && (sign1 != sign2)) : Bool)
  then
    (do
      ((Sail.BitVec.castWidth ) <$> (BFZero sign2 (Sail.BitVec.length op2))))
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
              ((Sail.BitVec.castWidth ) <$> (BFZero sign2 (Sail.BitVec.length op2))))
          else (pure (op2)))
      else
        (do
          let w__5 ← (( do (FPProcessNaNs type1 type2 op1_s op2_s fpcr) ) : SailM
            (Bool × (BitVec (2 * k_N))) )
          let (tup__0, tup__1) := (w__5 : (Bool × (BitVec (2 * k_N))))
          let done : Bool := tup__0
          let result : (BitVec (2 * k_N)) := tup__1
          let result ← (( do
            if ((! done) : Bool)
            then
              (do
                let fptype ← (( do (undefined_FPType (← occLabel 1896) ()) ) : SailM FPType )
                let sign ← (( do (undefined_bitvector_at (← occLabel 1897) 1) ) : SailM
                  (BitVec 1) )
                let value_name ← (( do (undefined_real_at (← occLabel 1898) ()) ) : SailM real )
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
                        ((Sail.BitVec.castWidth ) <$> (FPInfinity sign
                          (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))) ) : SailM
                        (BitVec (2 * k_N)) )
                      let result := (w__6 : (BitVec (2 * k_N)))
                      (pure ((fpcr, result))))
                  else
                    (do
                      if ((BEq.beq fptype FPType_Zero) : Bool)
                      then
                        (do
                          let sign : (BitVec 1) := (sign1 ||| sign2)
                          let w__7 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (FPZero sign
                              (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))) ) : SailM
                            (BitVec (2 * k_N)) )
                          let result := (w__7 : (BitVec (2 * k_N)))
                          (pure ((fpcr, result))))
                      else
                        (do
                          let fpcr : (BitVec 64) :=
                            if (altfp : Bool)
                            then (Sail.BitVec.updateSubrange fpcr 24 24 0#1)
                            else fpcr
                          let w__8 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (FPRoundBF value_name fpcr rounding fpexc
                              (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))) ) : SailM
                            (BitVec 32) )
                          let result := ((Sail.BitVec.castWidth w__8) : (BitVec (2 * k_N)))
                          (pure ((fpcr, result))))) ) : SailM ((BitVec 64) × (BitVec (2 * k_N))) )
                if (fpexc : Bool)
                then
                  (do
                    (FPProcessDenorms type1 type2 (2 *i (Sail.BitVec.length op2)) fpcr))
                else (pure (()))
                (pure (result)))
            else (pure (result)) ) : SailM (BitVec (2 * k_N)) )
          (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb result
              (Sail.Int.toNatChecked (((2 *i (Sail.BitVec.length op2)) -i 1)))
              (Sail.BitVec.length op2)))))))


/-- Type quantifiers: k_N : Nat, k_altfp : Bool, k_N = 16 -/
def BFMax__1 (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr_in : (BitVec 64)) (altfp : Bool) : SailM (BitVec k_N) := do
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 1901) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 1902) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 1903) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 1904) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 1905) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 1906) ()) ) : SailM real )
  ArmFull.assert ((Sail.BitVec.length op2) == 16) "sail-arm/v8_base.sail:32918.19-32918.20"
  let fpcr : FPCRType := fpcr_in
  let fpexc : Bool := true
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let done ← (( do (undefined_bool_at (← occLabel 1907) ()) ) : SailM Bool )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1908)
      (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))) ) : SailM (BitVec (2 * k_N)) )
  let op1_s : (BitVec (2 * k_N)) :=
    (Sail.BitVec.castWidth (op1 +++ (Zeros (n := (Sail.BitVec.length op2)))))
  let op2_s : (BitVec (2 * k_N)) :=
    (Sail.BitVec.castWidth (op2 +++ (Zeros (n := (Sail.BitVec.length op2)))))
  let w__0 ← (( do (FPUnpack__1 op1_s fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let type1 : FPType := tup__0
  let sign1 : (BitVec 1) := tup__1
  let value1_name : real := tup__2
  let w__1 ← (( do (FPUnpack__1 op2_s fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let type2 : FPType := tup__0
  let sign2 : (BitVec 1) := tup__1
  let value2_name : real := tup__2
  if ((((altfp && (BEq.beq type1 FPType_Zero)) && (BEq.beq type2 FPType_Zero)) && (sign1 != sign2)) : Bool)
  then
    (do
      ((Sail.BitVec.castWidth ) <$> (BFZero sign2 (Sail.BitVec.length op2))))
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
              ((Sail.BitVec.castWidth ) <$> (BFZero sign2 (Sail.BitVec.length op2))))
          else (pure (op2)))
      else
        (do
          let w__5 ← (( do (FPProcessNaNs type1 type2 op1_s op2_s fpcr) ) : SailM
            (Bool × (BitVec (2 * k_N))) )
          let (tup__0, tup__1) := (w__5 : (Bool × (BitVec (2 * k_N))))
          let done : Bool := tup__0
          let result : (BitVec (2 * k_N)) := tup__1
          let result ← (( do
            if ((! done) : Bool)
            then
              (do
                let fptype ← (( do (undefined_FPType (← occLabel 1909) ()) ) : SailM FPType )
                let sign ← (( do (undefined_bitvector_at (← occLabel 1910) 1) ) : SailM
                  (BitVec 1) )
                let value_name ← (( do (undefined_real_at (← occLabel 1911) ()) ) : SailM real )
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
                        ((Sail.BitVec.castWidth ) <$> (FPInfinity sign
                          (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))) ) : SailM
                        (BitVec (2 * k_N)) )
                      let result := (w__6 : (BitVec (2 * k_N)))
                      (pure ((fpcr, result))))
                  else
                    (do
                      if ((BEq.beq fptype FPType_Zero) : Bool)
                      then
                        (do
                          let sign : (BitVec 1) := (sign1 &&& sign2)
                          let w__7 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (FPZero sign
                              (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))) ) : SailM
                            (BitVec (2 * k_N)) )
                          let result := (w__7 : (BitVec (2 * k_N)))
                          (pure ((fpcr, result))))
                      else
                        (do
                          let fpcr : (BitVec 64) :=
                            if (altfp : Bool)
                            then (Sail.BitVec.updateSubrange fpcr 24 24 0#1)
                            else fpcr
                          let w__8 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (FPRoundBF value_name fpcr rounding fpexc
                              (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))) ) : SailM
                            (BitVec 32) )
                          let result := ((Sail.BitVec.castWidth w__8) : (BitVec (2 * k_N)))
                          (pure ((fpcr, result))))) ) : SailM ((BitVec 64) × (BitVec (2 * k_N))) )
                if (fpexc : Bool)
                then
                  (do
                    (FPProcessDenorms type1 type2 (2 *i (Sail.BitVec.length op2)) fpcr))
                else (pure (()))
                (pure (result)))
            else (pure (result)) ) : SailM (BitVec (2 * k_N)) )
          (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb result
              (Sail.Int.toNatChecked (((2 *i (Sail.BitVec.length op2)) -i 1)))
              (Sail.BitVec.length op2)))))))


end ArmFull.Functions
