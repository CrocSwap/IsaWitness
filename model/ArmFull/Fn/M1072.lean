import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0015
import ArmFull.Fn.M0016
import ArmFull.Fn.M0018
import ArmFull.Fn.M0020
import ArmFull.Fn.M0040
import ArmFull.Fn.M0051
import ArmFull.Fn.M0087
import ArmFull.Fn.M0116
import ArmFull.Fn.M0117
import ArmFull.Fn.M0120
import ArmFull.Fn.M0121
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0153
import ArmFull.Fn.M0154
import ArmFull.Fn.M0158
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0187
import ArmFull.Fn.M0203
import ArmFull.Fn.M0216
import ArmFull.Fn.M0226
import ArmFull.Fn.M0238
import ArmFull.Fn.M0253
import ArmFull.Fn.M0851
import ArmFull.Fn.M0852
import ArmFull.Fn.M0923
import ArmFull.Fn.M1002
import ArmFull.Fn.M1040
import ArmFull.Fn.M1041
import ArmFull.Fn.M1043
import ArmFull.Fn.M1044
import ArmFull.Fn.M1045
import ArmFull.Fn.M1046

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
def FPRSqrtStepFused (op1_in : (BitVec k_N)) (op2 : (BitVec k_N)) : SailM (BitVec k_N) := do
  let inf1 ← (( do (undefined_bool_at (← occLabel 1695) ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool_at (← occLabel 1696) ()) ) : SailM Bool )
  let result_value ← (( do (undefined_real_at (← occLabel 1697) ()) ) : SailM real )
  let sign ← (( do (undefined_bitvector_at (← occLabel 1698) 1) ) : SailM (BitVec 1) )
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 1699) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 1700) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 1701) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 1702) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 1703) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 1704) ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool_at (← occLabel 1705) ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool_at (← occLabel 1706) ()) ) : SailM Bool )
  ArmFull.assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length
          op2) == 64))) "sail-arm/v8_base.sail:29172.41-29172.42"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1707)
      (Sail.BitVec.length op2))) ) : SailM (BitVec k_N) )
  let op1 : (BitVec k_N) := op1_in
  let done ← (( do (undefined_bool_at (← occLabel 1708) ()) ) : SailM Bool )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let op1 ← (( do (FPNeg op1) ) : SailM (BitVec k_N) )
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
  let fpcr : (BitVec 64) :=
    if (altfp : Bool)
    then (Sail.BitVec.updateSubrange fpcr 23 22 0b00#2)
    else fpcr
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
  let w__3 ← (( do (FPProcessNaNs__1 type1 type2 op1 op2 fpcr fpexc) ) : SailM
    (Bool × (BitVec k_N)) )
  let (tup__0, tup__1) := (w__3 : (Bool × (BitVec k_N)))
  let done : Bool := tup__0
  let result : (BitVec k_N) := tup__1
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  if ((! done) : Bool)
  then
    (do
      let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
      let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
      let zero1 : Bool := (BEq.beq type1 FPType_Zero)
      let zero2 : Bool := (BEq.beq type2 FPType_Zero)
      if (((inf1 && zero2) || (zero1 && inf2)) : Bool)
      then
        (do
          ((Sail.BitVec.castWidth ) <$> (FPOnePointFive 0#1 (Sail.BitVec.length result))))
      else
        (do
          if ((inf1 || inf2) : Bool)
          then
            (do
              ((Sail.BitVec.castWidth ) <$> (FPInfinity (sign1 ^^^ sign2)
                (Sail.BitVec.length result))))
          else
            (do
              let result_value : real :=
                (div_real (add_real (3) (mult_real value1_name value2_name)) (2))
              if ((eq_real result_value (0)) : Bool)
              then
                (do
                  let sign : (BitVec 1) :=
                    if ((BEq.beq rounding FPRounding_NEGINF) : Bool)
                    then 1#1
                    else 0#1
                  ((Sail.BitVec.castWidth ) <$> (FPZero sign (Sail.BitVec.length result))))
              else
                (do
                  ((Sail.BitVec.castWidth ) <$> (FPRound__2 result_value fpcr rounding fpexc
                    (Sail.BitVec.length result)))))))
  else (pure (result))


/-- Type quantifiers: size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def MemNF_read (address : (BitVec 64)) (size : Nat) (accdesc : AccessDescriptor) : SailM ((BitVec (8 * size)) × Bool) := SailME.run do
  let c ← (( do (undefined_Constraint (← occLabel 1715) ()) ) : SailME
    ((BitVec (8 * size)) × Bool) Constraint )
  ArmFull.assert ((size == 1) || ((size == 2) || ((size == 4) || ((size == 8) || (size == 16))))) "sail-arm/v8_base.sail:29720.69-29720.70"
  let value_name ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1716)
      (Sail.Int.toNatChecked ((8 *i size))))) ) : SailME ((BitVec (8 * size)) × Bool)
    (BitVec (8 * size)) )
  let bad ← (( do (undefined_bool_at (← occLabel 1717) ()) ) : SailME
    ((BitVec (8 * size)) × Bool) Bool )
  let aligned : Bool := (IsAligned__1 address size)
  let w__1 ← (( do
    if (((! aligned) : Bool) : Bool)
    then
      (do
        (AlignmentEnforced ()))
    else (pure false) ) : SailME ((BitVec (8 * size)) × Bool) Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do
        ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits (Sail.Int.toNatChecked ((8 *i size))))) ) :
        SailME ((BitVec (8 * size)) × Bool) (BitVec (8 * size)) )
      (pure ((w__2, true))))
  else
    (do
      let atomic : Bool := (aligned || (size == 1))
      let value_name ← (( do
        if ((! atomic) : Bool)
        then
          (do
            let w__3 ← (( do (MemSingleNF_read address 1 accdesc aligned) ) : SailME
              ((BitVec (8 * size)) × Bool) ((BitVec (8 * 1)) × Bool) )
            let (tup__0, tup__1) := (w__3 : ((BitVec (8 * 1)) × Bool))
            let value_name : (BitVec (8 * size)) :=
              (Sail.BitVec.updateSubrange value_name 7 0 tup__0)
            let bad : Bool := tup__1
            if (bad : Bool)
            then
              (do
                let w__4 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits
                    (Sail.Int.toNatChecked ((8 *i size))))) ) : SailME ((BitVec (8 * size)) × Bool)
                  (BitVec (8 * size)) )
                SailME.throw ((w__4, true) : ((BitVec (8 * size)) × Bool))
                (pure (value_name)))
            else
              (do
                let aligned ← (( do
                  if ((! aligned) : Bool)
                  then
                    (do
                      let c ← (( do (ConstrainUnpredictable Unpredictable_DEVPAGE2) ) : SailME
                        ((BitVec (8 * size)) × Bool) Constraint )
                      ArmFull.assert ((BEq.beq c Constraint_FAULT) || (BEq.beq c Constraint_NONE)) "sail-arm/v8_base.sail:29735.63-29735.64"
                      let aligned : Bool :=
                        if ((BEq.beq c Constraint_NONE) : Bool)
                        then true
                        else aligned
                      (pure (aligned)))
                  else (pure (aligned)) ) : SailME ((BitVec (8 * size)) × Bool) Bool )
                let (bad, value_name) ← (( do
                  let loop_i_lower : Nat := 1
                  let loop_i_upper : Nat := (Sail.Int.toNatChecked ((size -i 1)))
                  (do
                    let mut loop_vars := (bad, value_name)
                    for i in [loop_i_lower:loop_i_upper:1]i do
                      let (bad, value_name) := loop_vars
                      loop_vars ← do
                        let w__5 ← (( do
                          (MemSingleNF_read (BitVec.addInt address i) 1 accdesc aligned) ) : SailME
                          ((BitVec (8 * size)) × Bool) ((BitVec (8 * 1)) × Bool) )
                        let (tup__0, tup__1) := (w__5 : ((BitVec (8 * 1)) × Bool))
                        let value_name : (BitVec (8 * size)) :=
                          (Sail.BitVec.updateSubrange value_name
                            (Sail.Int.toNatChecked (((8 *i i) +i 7)))
                            (Sail.Int.toNatChecked ((8 *i i))) (Sail.BitVec.castWidth tup__0))
                        let bad : Bool := tup__1
                        if (bad : Bool)
                        then
                          (do
                            let w__6 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits
                                (Sail.Int.toNatChecked ((8 *i size))))) ) : SailME
                              ((BitVec (8 * size)) × Bool) (BitVec (8 * size)) )
                            SailME.throw ((w__6, true) : ((BitVec (8 * size)) × Bool)))
                        else (pure (()))
                        (pure ((bad, value_name)))
                    (pure loop_vars)) ) : SailME ((BitVec (8 * size)) × Bool)
                  (Bool × (BitVec (8 * size))) )
                (pure (value_name))))
        else
          (do
            let w__7 ← (( do
              ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (MemSingleNF_read address size
                accdesc aligned)) ) : SailME ((BitVec (8 * size)) × Bool)
              ((BitVec (8 * size)) × Bool) )
            let (tup__0, tup__1) := (w__7 : ((BitVec (8 * size)) × Bool))
            let value_name : (BitVec (8 * size)) := tup__0
            let bad : Bool := tup__1
            if (bad : Bool)
            then
              (do
                let w__8 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits
                    (Sail.Int.toNatChecked ((8 *i size))))) ) : SailME ((BitVec (8 * size)) × Bool)
                  (BitVec (8 * size)) )
                SailME.throw ((w__8, true) : ((BitVec (8 * size)) × Bool)))
            else (pure (()))
            (pure (value_name))) ) : SailME ((BitVec (8 * size)) × Bool) (BitVec (8 * size)) )
      let w__9 ← (( do (BigEndian accdesc.acctype) ) : SailME ((BitVec (8 * size)) × Bool) Bool )
      let value_name : (BitVec (8 * size)) :=
        if (w__9 : Bool)
        then (reverse_endianness value_name)
        else value_name
      let value_name := value_name
      (pure ((value_name, false))))


/-- Type quantifiers: k_N : Nat, scale : Int, List.elem k_N [16, 32, 64] -/
def FPScale (op : (BitVec k_N)) (scale : Int) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fptype ← (( do (undefined_FPType (← occLabel 1731) ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector_at (← occLabel 1732) 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real_at (← occLabel 1733) ()) ) : SailM real )
  ArmFull.assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length
          op) == 64))) "sail-arm/v8_base.sail:29967.41-29967.42"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1734)
      (Sail.BitVec.length op))) ) : SailM (BitVec k_N) )
  let w__0 ← (( do (FPUnpack op fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let fptype : FPType := tup__0
  let sign : (BitVec 1) := tup__1
  let value_name : real := tup__2
  if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
  then
    (do
      (FPProcessNaN fptype op fpcr))
  else
    (do
      if ((BEq.beq fptype FPType_Zero) : Bool)
      then
        (do
          ((Sail.BitVec.castWidth ) <$> (FPZero sign (Sail.BitVec.length result))))
      else
        (do
          if ((BEq.beq fptype FPType_Infinity) : Bool)
          then
            (do
              ((Sail.BitVec.castWidth ) <$> (FPInfinity sign (Sail.BitVec.length result))))
          else
            (do
              let scale_opt : Int := (GetOptimizedScale op scale (Sail.BitVec.length result))
              let w__4 ← (( do
                ((Sail.BitVec.castWidth ) <$> (FPRound
                  (mult_real value_name (real_power (2) scale_opt)) fpcr (Sail.BitVec.length result)))
                ) : SailM (BitVec k_N) )
              let result := (w__4 : (BitVec k_N))
              (FPProcessDenorm fptype (Sail.BitVec.length result) fpcr)
              (pure (result)))))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPTrigSSel (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) : SailM (BitVec k_N) := do
  ArmFull.assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length
          op2) == 64))) "sail-arm/v8_base.sail:30017.41-30017.42"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1739)
      (Sail.BitVec.length op2))) ) : SailM (BitVec k_N) )
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op2 0)])) == 1#1) : Bool)
  then
    (do
      ((Sail.BitVec.castWidth ) <$> (FPOne
        (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op2 1)])) (Sail.BitVec.length result))))
  else
    (do
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op2 1)])) == 1#1) : Bool)
      then
        (do
          (FPNeg op1))
      else (pure (op1)))


/-- Type quantifiers: M : Nat, k_N : Nat, List.elem M [16, 32, 64] ∧ List.elem k_N [16, 32, 64] -/
def FPConvertSVE (op : (BitVec k_N)) (fpcr_in : (BitVec 64)) (rounding : FPRounding) (M : Nat) : SailM (BitVec M) := do
  let fpcr : FPCRType := fpcr_in
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 26 26 0#1)
  ((Sail.BitVec.castWidth ) <$> (FPConvert op fpcr rounding M))


/-- Type quantifiers: M : Nat, k_N : Nat, List.elem M [16, 32, 64] ∧ List.elem k_N [16, 32, 64] -/
def FPConvertSVE__1 (op : (BitVec k_N)) (fpcr_in : (BitVec 64)) (M : Nat) : SailM (BitVec M) := do
  let fpcr : FPCRType := fpcr_in
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 26 26 0#1)
  let w__0 ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  ((Sail.BitVec.castWidth ) <$> (FPConvert op fpcr w__0 M))


def GCSSS1 (incoming_pointer_name : (BitVec 64)) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (GCSEnabled w__0.EL) ) : SailM Bool )
  if ((! w__1) : Bool)
  then
    (do
      (EndOfInstruction ()))
  else (pure (()))
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let accdesc ← (( do (CreateAccDescGCSSS1 w__2.EL) ) : SailM AccessDescriptor )
  let outgoing_pointer ← (( do (GetCurrentGCSPointer ()) ) : SailM (BitVec 64) )
  let cmpoperand : (BitVec 64) :=
    ((Sail.BitVec.extractLsb incoming_pointer_name 63 12) +++ 0b000000000001#12)
  let operand : (BitVec 64) := ((Sail.BitVec.extractLsb outgoing_pointer 63 3) +++ 0b101#3)
  let data ← (( do (MemAtomic incoming_pointer_name cmpoperand operand accdesc) ) : SailM
    (BitVec 64) )
  if ((data == cmpoperand) : Bool)
  then
    (do
      (SetCurrentGCSPointer ((Sail.BitVec.extractLsb incoming_pointer_name 63 3) +++ 0b000#3)))
  else
    (do
      (GCSDataCheckException GCSInstType_SS1))


/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def BFMulAddH (addend : (BitVec k_N)) (op1 : (BitVec (k_N / 2))) (op2 : (BitVec (k_N / 2))) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  ArmFull.assert ((Sail.BitVec.length addend) == 32) "sail-arm/v8_base.sail:32181.19-32181.20"
  let value1_name : (BitVec k_N) :=
    (Sail.BitVec.castWidth (op1 +++ (Zeros
        (n := (Sail.Int.toNatChecked ((Int.ediv (Sail.BitVec.length addend) 2)))))))
  let value2_name : (BitVec k_N) :=
    (Sail.BitVec.castWidth (op2 +++ (Zeros
        (n := (Sail.Int.toNatChecked ((Int.ediv (Sail.BitVec.length value1_name) 2)))))))
  let fpcr : FPCRType := fpcr_in
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
  let fpcr : (BitVec 64) :=
    if (altfp : Bool)
    then (Sail.BitVec.updateSubrange fpcr 23 22 0b00#2)
    else fpcr
  (FPMulAdd__1 addend value1_name value2_name fpcr fpexc)


/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def FPConvertBF__1 (op : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec (k_N / 2)) := do
  let w__0 ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  ((Sail.BitVec.castWidth ) <$> (FPConvertBF (k_N := 32) (Sail.BitVec.castWidth op) fpcr w__0))


/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def BFDotAdd (addend : (BitVec k_N)) (op1_a : (BitVec (k_N / 2))) (op1_b : (BitVec (k_N / 2))) (op2_a : (BitVec (k_N / 2))) (op2_b : (BitVec (k_N / 2))) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  ArmFull.assert ((Sail.BitVec.length addend) == 32) "sail-arm/v8_base.sail:32396.19-32396.20"
  let fpcr : FPCRType := fpcr_in
  let prod ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1824)
      (Sail.BitVec.length addend))) ) : SailM (BitVec k_N) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1825)
      (Sail.BitVec.length prod))) ) : SailM (BitVec k_N) )
  let w__1 ← (( do
    (pure ((← do
          let w__0 ← (( do (HaveEBF16 ()) ) : SailM Bool )
          (pure (((! w__0) : Bool)))) || (((_get_FPCRType_EBF fpcr) == 0#1) : Bool))) ) : SailM Bool
    )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do
        ((Sail.BitVec.castWidth ) <$> (BFMulH (k_N := 16) (Sail.BitVec.castWidth op1_a)
          (Sail.BitVec.castWidth op2_a))) ) : SailM (BitVec (2 * 16)) )
      let w__3 ← (( do
        ((Sail.BitVec.castWidth ) <$> (BFMulH (k_N := 16) (Sail.BitVec.castWidth op1_b)
          (Sail.BitVec.castWidth op2_b))) ) : SailM (BitVec (2 * 16)) )
      let prod ← (( do ((Sail.BitVec.castWidth ) <$> ((FPAdd_BF16 (k_N := 32) w__2 w__3))) ) :
        SailM (BitVec k_N) )
      ((Sail.BitVec.castWidth ) <$> (FPAdd_BF16 (k_N := 32) (Sail.BitVec.castWidth addend)
        (Sail.BitVec.castWidth prod))))
  else
    (do
      let isbfloat16 : Bool := true
      let fpexc : Bool := false
      let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 25 25 1#1)
      let prod ← (( do
        ((Sail.BitVec.castWidth ) <$> ((FPDot__1 (k_N := 32) (Sail.BitVec.castWidth op1_a)
          (Sail.BitVec.castWidth op1_b) (Sail.BitVec.castWidth op2_a) (Sail.BitVec.castWidth op2_b)
          fpcr isbfloat16 fpexc))) ) : SailM (BitVec k_N) )
      (FPAdd__1 addend prod fpcr fpexc))


/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFAdd (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := true
  ((Sail.BitVec.castWidth ) <$> (BFAdd__1 (k_N := 16) (Sail.BitVec.castWidth op1)
    (Sail.BitVec.castWidth op2) fpcr fpexc))


/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFAdd_ZA (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := false
  let fpcr : FPCRType := fpcr_in
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 25 25 1#1)
  ((Sail.BitVec.castWidth ) <$> (BFAdd__1 (k_N := 16) (Sail.BitVec.castWidth op1)
    (Sail.BitVec.castWidth op2) fpcr fpexc))


/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFSub (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := true
  ((Sail.BitVec.castWidth ) <$> (BFSub__1 (k_N := 16) (Sail.BitVec.castWidth op1)
    (Sail.BitVec.castWidth op2) fpcr fpexc))


/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFSub_ZA (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := false
  let fpcr : FPCRType := fpcr_in
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 25 25 1#1)
  ((Sail.BitVec.castWidth ) <$> (BFSub__1 (k_N := 16) (Sail.BitVec.castWidth op1)
    (Sail.BitVec.castWidth op2) fpcr fpexc))


/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFMulAdd (addend : (BitVec k_N)) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := true
  ((Sail.BitVec.castWidth ) <$> (BFMulAdd__1 (k_N := 16) (Sail.BitVec.castWidth addend)
    (Sail.BitVec.castWidth op1) (Sail.BitVec.castWidth op2) fpcr fpexc))


/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFMulAdd_ZA (addend : (BitVec k_N)) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := false
  let fpcr : FPCRType := fpcr_in
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 25 25 1#1)
  ((Sail.BitVec.castWidth ) <$> (BFMulAdd__1 (k_N := 16) (Sail.BitVec.castWidth addend)
    (Sail.BitVec.castWidth op1) (Sail.BitVec.castWidth op2) fpcr fpexc))


/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFMul (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := true
  ((Sail.BitVec.castWidth ) <$> (BFMul__1 (k_N := 16) (Sail.BitVec.castWidth op1)
    (Sail.BitVec.castWidth op2) fpcr fpexc))


/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFMin (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let altfp ← (( do
    (pure ((← do
          if ((← do
               (HaveAltFP ())) : Bool)
          then
            (do
              let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              (pure (((! w__1) : Bool))))
          else (pure false)) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  ((Sail.BitVec.castWidth ) <$> (BFMin__1 (k_N := 16) (Sail.BitVec.castWidth op1)
    (Sail.BitVec.castWidth op2) fpcr altfp))


/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFMinNum (op1_in : (BitVec k_N)) (op2_in : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let type1 ← (( do (undefined_FPType (← occLabel 1899) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 1900) ()) ) : SailM FPType )
  ArmFull.assert ((Sail.BitVec.length op2_in) == 16) "sail-arm/v8_base.sail:32871.19-32871.20"
  let fpexc : Bool := true
  let isbfloat16 : Bool := true
  let op1 : (BitVec k_N) := op1_in
  let op2 : (BitVec k_N) := op2_in
  let altfp ← (( do
    (pure ((← do
          if ((← do
               (HaveAltFP ())) : Bool)
          then
            (do
              let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              (pure (((! w__1) : Bool))))
          else (pure false)) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  let (__tup_0, _, _) ← (( do (FPUnpackBase__1 op1 fpcr fpexc isbfloat16) ) : SailM
    (FPType × (BitVec 1) × real) )
  let type1 : FPType := __tup_0
  let (__tup_0, _, _) ← (( do (FPUnpackBase__1 op2 fpcr fpexc isbfloat16) ) : SailM
    (FPType × (BitVec 1) × real) )
  let type2 : FPType := __tup_0
  let type1_nan : Bool := ((BEq.beq type1 FPType_QNaN) || (BEq.beq type1 FPType_SNaN))
  let type2_nan : Bool := ((BEq.beq type2 FPType_QNaN) || (BEq.beq type2 FPType_SNaN))
  let (op1, op2) ← (( do
    if ((! ((altfp && type1_nan) && type2_nan)) : Bool)
    then
      (do
        if (((BEq.beq type1 FPType_QNaN) && (bne type2 FPType_QNaN)) : Bool)
        then
          (do
            let w__3 ← (( do
              ((Sail.BitVec.castWidth ) <$> (BFInfinity 0#1 (Sail.BitVec.length op2_in))) ) : SailM
              (BitVec 16) )
            let op1 := ((Sail.BitVec.castWidth w__3) : (BitVec k_N))
            (pure ((op1, op2))))
        else
          (do
            let op2 ← (( do
              if (((bne type1 FPType_QNaN) && (BEq.beq type2 FPType_QNaN)) : Bool)
              then
                (do
                  ((Sail.BitVec.castWidth ) <$> (BFInfinity 0#1 (Sail.BitVec.length op2_in))))
              else (pure (op2)) ) : SailM (BitVec k_N) )
            (pure ((op1, op2)))))
    else (pure ((op1, op2))) ) : SailM ((BitVec k_N) × (BitVec k_N)) )
  let altfmaxfmin : Bool := false
  ((Sail.BitVec.castWidth ) <$> (BFMin__1 (k_N := 16) (Sail.BitVec.castWidth op1)
    (Sail.BitVec.castWidth op2) fpcr altfmaxfmin))


/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFMax (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let altfp ← (( do
    (pure ((← do
          if ((← do
               (HaveAltFP ())) : Bool)
          then
            (do
              let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              (pure (((! w__1) : Bool))))
          else (pure false)) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  ((Sail.BitVec.castWidth ) <$> (BFMax__1 (k_N := 16) (Sail.BitVec.castWidth op1)
    (Sail.BitVec.castWidth op2) fpcr altfp))


/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFMaxNum (op1_in : (BitVec k_N)) (op2_in : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let type1 ← (( do (undefined_FPType (← occLabel 1912) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 1913) ()) ) : SailM FPType )
  ArmFull.assert ((Sail.BitVec.length op2_in) == 16) "sail-arm/v8_base.sail:32968.19-32968.20"
  let fpexc : Bool := true
  let isbfloat16 : Bool := true
  let op1 : (BitVec k_N) := op1_in
  let op2 : (BitVec k_N) := op2_in
  let altfp ← (( do
    (pure ((← do
          if ((← do
               (HaveAltFP ())) : Bool)
          then
            (do
              let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              (pure (((! w__1) : Bool))))
          else (pure false)) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  let (__tup_0, _, _) ← (( do (FPUnpackBase__1 op1 fpcr fpexc isbfloat16) ) : SailM
    (FPType × (BitVec 1) × real) )
  let type1 : FPType := __tup_0
  let (__tup_0, _, _) ← (( do (FPUnpackBase__1 op2 fpcr fpexc isbfloat16) ) : SailM
    (FPType × (BitVec 1) × real) )
  let type2 : FPType := __tup_0
  let type1_nan : Bool := ((BEq.beq type1 FPType_QNaN) || (BEq.beq type1 FPType_SNaN))
  let type2_nan : Bool := ((BEq.beq type2 FPType_QNaN) || (BEq.beq type2 FPType_SNaN))
  let (op1, op2) ← (( do
    if ((! ((altfp && type1_nan) && type2_nan)) : Bool)
    then
      (do
        if (((BEq.beq type1 FPType_QNaN) && (bne type2 FPType_QNaN)) : Bool)
        then
          (do
            let w__3 ← (( do
              ((Sail.BitVec.castWidth ) <$> (BFInfinity 1#1 (Sail.BitVec.length op2_in))) ) : SailM
              (BitVec 16) )
            let op1 := ((Sail.BitVec.castWidth w__3) : (BitVec k_N))
            (pure ((op1, op2))))
        else
          (do
            let op2 ← (( do
              if (((bne type1 FPType_QNaN) && (BEq.beq type2 FPType_QNaN)) : Bool)
              then
                (do
                  ((Sail.BitVec.castWidth ) <$> (BFInfinity 1#1 (Sail.BitVec.length op2_in))))
              else (pure (op2)) ) : SailM (BitVec k_N) )
            (pure ((op1, op2)))))
    else (pure ((op1, op2))) ) : SailM ((BitVec k_N) × (BitVec k_N)) )
  let altfmaxfmin : Bool := false
  ((Sail.BitVec.castWidth ) <$> (BFMax__1 (k_N := 16) (Sail.BitVec.castWidth op1)
    (Sail.BitVec.castWidth op2) fpcr altfmaxfmin))


/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def FPDotAdd (addend : (BitVec k_N)) (op1_a : (BitVec (k_N / 2))) (op1_b : (BitVec (k_N / 2))) (op2_a : (BitVec (k_N / 2))) (op2_b : (BitVec (k_N / 2))) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  ArmFull.assert ((Sail.BitVec.length addend) == 32) "sail-arm/v8_base.sail:33025.19-33025.20"
  let isbfloat16 : Bool := false
  let fpexc : Bool := true
  let prod ← (( do
    ((Sail.BitVec.castWidth ) <$> ((FPDot__1 (k_N := 32) (Sail.BitVec.castWidth op1_a)
      (Sail.BitVec.castWidth op1_b) (Sail.BitVec.castWidth op2_a) (Sail.BitVec.castWidth op2_b) fpcr
      isbfloat16 fpexc))) ) : SailM (BitVec k_N) )
  (FPAdd__1 addend prod fpcr fpexc)


/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def FPDotAdd_ZA (addend : (BitVec k_N)) (op1_a : (BitVec (k_N / 2))) (op1_b : (BitVec (k_N / 2))) (op2_a : (BitVec (k_N / 2))) (op2_b : (BitVec (k_N / 2))) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpcr : FPCRType := fpcr_in
  ArmFull.assert ((Sail.BitVec.length addend) == 32) "sail-arm/v8_base.sail:33038.19-33038.20"
  let isbfloat16 : Bool := false
  let fpexc : Bool := false
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 25 25 1#1)
  let prod ← (( do
    ((Sail.BitVec.castWidth ) <$> ((FPDot__1 (k_N := 32) (Sail.BitVec.castWidth op1_a)
      (Sail.BitVec.castWidth op1_b) (Sail.BitVec.castWidth op2_a) (Sail.BitVec.castWidth op2_b) fpcr
      isbfloat16 fpexc))) ) : SailM (BitVec k_N) )
  (FPAdd__1 addend prod fpcr fpexc)


def SPEPostExecution (_ : Unit) : SailM Unit := do
  let w__0 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      writeReg SPESampleInFlight false
      (PMUEvent PMU_EVENT_SAMPLE_FEED)
      let loop_counter_index_lower : Nat := 0
      let loop_counter_index_upper : Nat := (Sail.Int.toNatChecked ((SPEMaxCounters -i 1)))
      (do
        let mut loop_vars := ()
        for counter_index in [loop_counter_index_lower:loop_counter_index_upper:1]i do
          let () := loop_vars
          loop_vars ← do
            let w__1 ← (( do readReg SPESampleCounterPending ) : SailM (Vector Bool 32) )
            if ((GetElem?.getElem! w__1 (Sail.Int.toNatChecked (counter_index))) : Bool)
            then
              (do
                (SPEStopCounter (Sail.Int.toNatChecked (counter_index))))
            else (pure (()))
        (pure loop_vars))
      let discard : Bool := false
      let w__2 ← (( do (HaveStatisticalProfilingv1p2 ()) ) : SailM Bool )
      let discard ← (( do
        if (w__2 : Bool)
        then
          (do
            let w__3 ← (( do readReg PMBLIMITR_EL1 ) : SailM (BitVec 64) )
            let discard := (((_get_PMBLIMITR_EL1_Type_FM w__3) == 0b10#2) : Bool)
            (pure (discard)))
        else (pure (discard)) ) : SailM Bool )
      let w__8 ← (( do
        (pure ((← do
              let w__4 ← (( do readReg SPESampleEvents ) : SailM (BitVec 64) )
              let w__5 ← (( do readReg SPESampleCounter ) : SailM (Vector Int 32) )
              let w__6 ← (( do readReg SPESampleOpType ) : SailM OpType )
              (SPECollectRecord w__4 (GetElem?.getElem! w__5 SPECounterPosTotalLatency) w__6)) && ((! discard) : Bool)))
        ) : SailM Bool )
      if (w__8 : Bool)
      then
        (do
          (SPEConstructRecord ())
          let w__9 ← (( do (SPEBufferIsFull ()) ) : SailM Bool )
          if (w__9 : Bool)
          then
            (do
              (SPEBufferFilled ()))
          else (pure (())))
      else (pure (()))
      (SPEResetSampleStorage ()))
  else (pure (()))


end ArmFull.Functions
