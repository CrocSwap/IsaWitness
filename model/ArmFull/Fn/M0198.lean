import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0036
import ArmFull.Fn.M0040
import ArmFull.Fn.M0041
import ArmFull.Fn.M0043
import ArmFull.Fn.M0047
import ArmFull.Fn.M0048
import ArmFull.Fn.M0049
import ArmFull.Fn.M0113
import ArmFull.Fn.M0117
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
import ArmFull.Fn.M0184
import ArmFull.Fn.M0185
import ArmFull.Fn.M0186
import ArmFull.Fn.M0187
import ArmFull.Fn.M0188

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

def IsFullA64Enabled (_ : Unit) : SailM Bool := SailME.run do
  let w__0 ← (( do (HaveSMEFullA64 ()) ) : SailME Bool Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let w__5 ← (( do
        if ((← do
             if ((← do
                  let w__1 ← (( do readReg PSTATE ) : SailME Bool ProcState )
                  (pure (((w__1.EL == EL0) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__2 ← (( do readReg PSTATE ) : SailME Bool ProcState )
                 (pure (((w__2.EL == EL1) : Bool))))) : Bool)
        then
          (do
            let w__4 ← (( do (IsInHost ()) ) : SailME Bool Bool )
            (pure (((! w__4) : Bool))))
        else (pure false) ) : SailME Bool Bool )
      if (w__5 : Bool)
      then
        (do
          let w__6 ← (( do readReg SMCR_EL1 ) : SailME Bool (BitVec 64) )
          if (((_get_SMCR_EL1_Type_FA64 w__6) == 0#1) : Bool)
          then
            (do
              SailME.throw (false : Bool))
          else (pure (())))
      else (pure (()))
      let w__13 ← (( do
        if ((← do
             if ((← do
                  let w__7 ← (( do readReg PSTATE ) : SailME Bool ProcState )
                  (pure (((w__7.EL == EL0) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 if ((← do
                      let w__8 ← (( do readReg PSTATE ) : SailME Bool ProcState )
                      (pure (((w__8.EL == EL1) : Bool)))) : Bool)
                 then (pure true)
                 else
                   (do
                     let w__9 ← (( do readReg PSTATE ) : SailME Bool ProcState )
                     (pure (((w__9.EL == EL2) : Bool)))))) : Bool)
        then
          (do
            (EL2Enabled ()))
        else (pure false) ) : SailME Bool Bool )
      if (w__13 : Bool)
      then
        (do
          let w__14 ← (( do readReg SMCR_EL2 ) : SailME Bool (BitVec 64) )
          if (((_get_SMCR_EL2_Type_FA64 w__14) == 0#1) : Bool)
          then
            (do
              SailME.throw (false : Bool))
          else (pure (())))
      else (pure (()))
      if ((HaveEL EL3) : Bool)
      then
        (do
          let w__15 ← (( do readReg SMCR_EL3 ) : SailME Bool (BitVec 64) )
          if (((_get_SMCR_EL3_Type_FA64 w__15) == 0#1) : Bool)
          then
            (do
              SailME.throw (false : Bool))
          else (pure (())))
      else (pure (()))
      (pure (true)))


def CNTP_CTL_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_CNTP_CTL_Type (← occLabel 1159) ()) ) : SailM CNTP_CTL_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      readReg CNTP_CTL_S)
  else
    (do
      (CNTP_CTL_NS_read ()))


def CNTP_CTL_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTP_CTL_Type := value_name
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      writeReg CNTP_CTL_S r)
  else
    (do
      (CNTP_CTL_NS_write r))


def CNTP_CVAL_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do (undefined_CNTP_CVAL_Type (← occLabel 1162) ()) ) : SailM CNTP_CVAL_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      readReg CNTP_CVAL_S)
  else
    (do
      (CNTP_CVAL_NS_read ()))


def AArch64_CheckTimerConditions (_ : Unit) : SailM Unit := do
  let status ← (( do (undefined_bool_at (.site 1174) ()) ) : SailM Bool )
  let offset ← (( do (undefined_bitvector_at (.site 1175) 64) ) : SailM (BitVec 64) )
  let imask ← (( do (undefined_bitvector_at (.site 1176) 1) ) : SailM (BitVec 1) )
  let ss ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
  let ecv : Bool := false
  let w__0 ← (( do (HaveECVExt ()) ) : SailM Bool )
  let ecv ← (( do
    if (w__0 : Bool)
    then
      (do
        if ((← do
             if ((← do
                  let w__1 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_CNTHCTL_EL2_Type_ECV w__1) == 1#1) : Bool)))) : Bool)
             then
               (do
                 let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                 (pure ((((_get_SCR_EL3_Type_ECVEn w__2) == 1#1) : Bool))))
             else (pure false)) : Bool)
        then
          (do
            (EL2Enabled ()))
        else (pure false))
    else (pure (ecv)) ) : SailM Bool )
  let offset ← (( do
    if (ecv : Bool)
    then
      (do
        readReg CNTPOFF_EL2)
    else
      (let offset : (BitVec 64) := (Zeros (n := 64))
      (pure (offset))) ) : SailM (BitVec 64) )
  let w__7 ← (( do readReg CNTP_CTL_EL0 ) : SailM (BitVec 64) )
  let (imask, status) ← (( do
    if (((_get_CNTP_CTL_EL0_Type_ENABLE w__7) == 1#1) : Bool)
    then
      (do
        let w__8 ← (( do readReg CNTP_CTL_EL0 ) : SailM (BitVec 64) )
        let imask := ((_get_CNTP_CTL_EL0_Type_IMASK w__8) : (BitVec 1))
        let w__12 ← (( do
          if ((← do
               (pure ((← do
                     (HaveRME ())) && (((BEq.beq ss SS_Root) || (BEq.beq ss SS_Realm)) : Bool)))) : Bool)
          then
            (do
              let w__11 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_CNTHCTL_EL2_Type_CNTPMASK w__11) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let imask : (BitVec 1) :=
          if (w__12 : Bool)
          then 1#1
          else imask
        let w__13 ← (( do readReg CNTP_CVAL_EL0 ) : SailM (BitVec 64) )
        let w__14 ← (( do (IsTimerConditionMet offset w__13 imask InterruptID_CNTP) ) : SailM Bool
          )
        let status := (w__14 : Bool)
        let w__15 ← (( do readReg CNTP_CTL_EL0 ) : SailM (BitVec 64) )
        writeReg CNTP_CTL_EL0 (Sail.BitVec.updateSubrange w__15 2 2
          (if (status : Bool)
          then 1#1
          else 0#1))
        (pure ((imask, status))))
    else (pure ((imask, status))) ) : SailM ((BitVec 1) × Bool) )
  let w__20 ← (( do
    if ((← do
         if (((HaveEL EL3) : Bool) : Bool)
         then (pure true)
         else
           (do
             if (((HaveEL EL2) : Bool) : Bool)
             then
               (do
                 let w__16 ← (( do (HaveSecureEL2Ext ()) ) : SailM Bool )
                 (pure (((! w__16) : Bool))))
             else (pure false))) : Bool)
    then
      (do
        let w__19 ← (( do readReg CNTHP_CTL_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_CNTHP_CTL_EL2_Type_ENABLE w__19) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let status ← (( do
    if (w__20 : Bool)
    then
      (do
        let w__21 ← (( do readReg CNTHP_CVAL_EL2 ) : SailM (BitVec 64) )
        let w__22 ← (( do readReg CNTHP_CTL_EL2 ) : SailM (BitVec 64) )
        let w__23 ← (( do
          (IsTimerConditionMet (Zeros (n := 64)) w__21 (_get_CNTHP_CTL_EL2_Type_IMASK w__22)
            InterruptID_CNTHP) ) : SailM Bool )
        let status := (w__23 : Bool)
        let w__24 ← (( do readReg CNTHP_CTL_EL2 ) : SailM (BitVec 64) )
        writeReg CNTHP_CTL_EL2 (Sail.BitVec.updateSubrange w__24 2 2
          (if (status : Bool)
          then 1#1
          else 0#1))
        (pure (status)))
    else (pure (status)) ) : SailM Bool )
  let w__28 ← (( do
    if ((← do
         if (((HaveEL EL2) : Bool) : Bool)
         then
           (do
             (HaveSecureEL2Ext ()))
         else (pure false)) : Bool)
    then
      (do
        let w__27 ← (( do readReg CNTHPS_CTL_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_CNTHPS_CTL_EL2_Type_ENABLE w__27) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let status ← (( do
    if (w__28 : Bool)
    then
      (do
        let w__29 ← (( do readReg CNTHPS_CVAL_EL2 ) : SailM (BitVec 64) )
        let w__30 ← (( do readReg CNTHPS_CTL_EL2 ) : SailM (BitVec 64) )
        let w__31 ← (( do
          (IsTimerConditionMet (Zeros (n := 64)) w__29 (_get_CNTHPS_CTL_EL2_Type_IMASK w__30)
            InterruptID_CNTHPS) ) : SailM Bool )
        let status := (w__31 : Bool)
        let w__32 ← (( do readReg CNTHPS_CTL_EL2 ) : SailM (BitVec 64) )
        writeReg CNTHPS_CTL_EL2 (Sail.BitVec.updateSubrange w__32 2 2
          (if (status : Bool)
          then 1#1
          else 0#1))
        (pure (status)))
    else (pure (status)) ) : SailM Bool )
  let w__33 ← (( do readReg CNTPS_CTL_EL1 ) : SailM (BitVec 64) )
  let status ← (( do
    if (((_get_CNTPS_CTL_EL1_Type_ENABLE w__33) == 1#1) : Bool)
    then
      (do
        let w__34 ← (( do readReg CNTPS_CVAL_EL1 ) : SailM (BitVec 64) )
        let w__35 ← (( do readReg CNTPS_CTL_EL1 ) : SailM (BitVec 64) )
        let w__36 ← (( do
          (IsTimerConditionMet offset w__34 (_get_CNTPS_CTL_EL1_Type_IMASK w__35) InterruptID_CNTPS)
          ) : SailM Bool )
        let status := (w__36 : Bool)
        let w__37 ← (( do readReg CNTPS_CTL_EL1 ) : SailM (BitVec 64) )
        writeReg CNTPS_CTL_EL1 (Sail.BitVec.updateSubrange w__37 2 2
          (if (status : Bool)
          then 1#1
          else 0#1))
        (pure (status)))
    else (pure (status)) ) : SailM Bool )
  let w__38 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
  let status ← (( do
    if (((_get_CNTV_CTL_EL0_Type_ENABLE w__38) == 1#1) : Bool)
    then
      (do
        let w__39 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
        let imask : (BitVec 1) := ((_get_CNTV_CTL_EL0_Type_IMASK w__39) : (BitVec 1))
        let w__43 ← (( do
          if ((← do
               (pure ((← do
                     (HaveRME ())) && (((BEq.beq ss SS_Root) || (BEq.beq ss SS_Realm)) : Bool)))) : Bool)
          then
            (do
              let w__42 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_CNTHCTL_EL2_Type_CNTVMASK w__42) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let imask : (BitVec 1) :=
          if (w__43 : Bool)
          then 1#1
          else imask
        let w__44 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
        let w__45 ← (( do readReg CNTV_CVAL_EL0 ) : SailM (BitVec 64) )
        let w__46 ← (( do (IsTimerConditionMet w__44 w__45 imask InterruptID_CNTV) ) : SailM Bool
          )
        let status := (w__46 : Bool)
        let w__47 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
        writeReg CNTV_CTL_EL0 (Sail.BitVec.updateSubrange w__47 2 2
          (if (status : Bool)
          then 1#1
          else 0#1))
        (pure (status)))
    else (pure (status)) ) : SailM Bool )
  let w__53 ← (( do
    if ((← do
         if ((← do
              (HaveVirtHostExt ())) : Bool)
         then
           (do
             if (((HaveEL EL3) : Bool) : Bool)
             then (pure true)
             else
               (do
                 let w__49 ← (( do (HaveSecureEL2Ext ()) ) : SailM Bool )
                 (pure (((! w__49) : Bool)))))
         else (pure false)) : Bool)
    then
      (do
        let w__52 ← (( do readReg CNTHV_CTL_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_CNTHV_CTL_EL2_Type_ENABLE w__52) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let status ← (( do
    if (w__53 : Bool)
    then
      (do
        let w__54 ← (( do readReg CNTHV_CVAL_EL2 ) : SailM (BitVec 64) )
        let w__55 ← (( do readReg CNTHV_CTL_EL2 ) : SailM (BitVec 64) )
        let w__56 ← (( do
          (IsTimerConditionMet (Zeros (n := 64)) w__54 (_get_CNTHV_CTL_EL2_Type_IMASK w__55)
            InterruptID_CNTHV) ) : SailM Bool )
        let status := (w__56 : Bool)
        let w__57 ← (( do readReg CNTHV_CTL_EL2 ) : SailM (BitVec 64) )
        writeReg CNTHV_CTL_EL2 (Sail.BitVec.updateSubrange w__57 2 2
          (if (status : Bool)
          then 1#1
          else 0#1))
        (pure (status)))
    else (pure (status)) ) : SailM Bool )
  let w__62 ← (( do
    if ((← do
         if ((← do
              (HaveSecureEL2Ext ())) : Bool)
         then
           (do
             (HaveVirtHostExt ()))
         else (pure false)) : Bool)
    then
      (do
        let w__61 ← (( do readReg CNTHVS_CTL_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_CNTHVS_CTL_EL2_Type_ENABLE w__61) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__62 : Bool)
  then
    (do
      let w__63 ← (( do readReg CNTHVS_CVAL_EL2 ) : SailM (BitVec 64) )
      let w__64 ← (( do readReg CNTHVS_CTL_EL2 ) : SailM (BitVec 64) )
      let status ← (( do
        (IsTimerConditionMet (Zeros (n := 64)) w__63 (_get_CNTHVS_CTL_EL2_Type_IMASK w__64)
          InterruptID_CNTHVS) ) : SailM Bool )
      let w__65 ← (( do readReg CNTHVS_CTL_EL2 ) : SailM (BitVec 64) )
      writeReg CNTHVS_CTL_EL2 (Sail.BitVec.updateSubrange w__65 2 2
        (if (status : Bool)
        then 1#1
        else 0#1)))
  else (pure (()))


def AArch64_S1E0POEnabled (regime : Regime) (nv1 : (BitVec 1)) : SailM Bool := do
  ArmFull.assert (HasUnprivileged regime) "sail-arm/v8_base.sail:24025.34-24025.35"
  let w__0 ← (( do (HaveS1POExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      match regime with
      | .Regime_EL20 =>
        (do
          if ((← do
               (IsTCR2EL2Enabled ())) : Bool)
          then
            (do
              let w__2 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_TCR2_EL2_Type_E0POE w__2) == 1#1) : Bool))))
          else (pure false))
      | .Regime_EL10 =>
        (do
          if ((← do
               (pure ((← do
                     (IsTCR2EL1Enabled ())) && ((nv1 == 0#1) : Bool)))) : Bool)
          then
            (do
              let w__6 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
              (pure ((((_get_TCR2_EL1_Type_E0POE w__6) == 1#1) : Bool))))
          else (pure false))
      | _ =>
        (do
          (undefined_bool_at (← occLabel 1420) ())))


def AArch64_S1POEnabled (regime : Regime) : SailM Bool := do
  let w__0 ← (( do (HaveS1POExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      match regime with
      | .Regime_EL3 =>
        (do
          let w__1 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
          (pure (((_get_TCR_EL3_Type_POE w__1) == 1#1))))
      | .Regime_EL2 =>
        (do
          if ((← do
               (IsTCR2EL2Enabled ())) : Bool)
          then
            (do
              let w__3 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_TCR2_EL2_Type_POE w__3) == 1#1) : Bool))))
          else (pure false))
      | .Regime_EL20 =>
        (do
          if ((← do
               (IsTCR2EL2Enabled ())) : Bool)
          then
            (do
              let w__6 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_TCR2_EL2_Type_POE w__6) == 1#1) : Bool))))
          else (pure false))
      | .Regime_EL10 =>
        (do
          if ((← do
               (IsTCR2EL1Enabled ())) : Bool)
          then
            (do
              let w__9 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
              (pure ((((_get_TCR2_EL1_Type_POE w__9) == 1#1) : Bool))))
          else (pure false))
      | _ =>
        (do
          (undefined_bool_at (← occLabel 1453) ())))


/-- Type quantifiers: k_s1aarch64 : Bool -/
def AArch64_RLS2TTWParams (s1aarch64 : Bool) : SailM S2TTWParams := do
  let walkparams ← (( do (AArch64_NSS2TTWParams s1aarch64) ) : SailM S2TTWParams )
  let w__2 ← (( do
    if ((← do
         (HaveFeatMEC ())) : Bool)
    then
      (do
        (IsSCTLR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let w__4 ← (( do
    if (w__2 : Bool)
    then
      (do
        let w__3 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_SCTLR2_EL2_Type_EMEC w__3))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with emec := w__4 } : S2TTWParams)
  (pure (walkparams))


def IsD128Enabled (el : (BitVec 2)) : SailM Bool := do
  let d128enabled ← (( do (undefined_bool_at (← occLabel 1657) ()) ) : SailM Bool )
  let w__0 ← (( do (Have128BitDescriptorExt ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let questionMark := el
      if ((questionMark == EL0) : Bool)
      then
        (do
          let w__1 ← (( do (ELIsInHost EL0) ) : SailM Bool )
          if ((! w__1) : Bool)
          then
            (do
              if ((← do
                   (IsTCR2EL1Enabled ())) : Bool)
              then
                (do
                  let w__3 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
                  (pure ((((_get_TCR2_EL1_Type_D128 w__3) == 1#1) : Bool))))
              else (pure false))
          else
            (do
              if ((← do
                   (IsTCR2EL2Enabled ())) : Bool)
              then
                (do
                  let w__6 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_TCR2_EL2_Type_D128 w__6) == 1#1) : Bool))))
              else (pure false)))
      else
        (do
          if ((questionMark == EL1) : Bool)
          then
            (do
              if ((← do
                   (IsTCR2EL1Enabled ())) : Bool)
              then
                (do
                  let w__9 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
                  (pure ((((_get_TCR2_EL1_Type_D128 w__9) == 1#1) : Bool))))
              else (pure false))
          else
            (do
              if ((questionMark == EL2) : Bool)
              then
                (do
                  if ((← do
                       if ((← do
                            (IsTCR2EL2Enabled ())) : Bool)
                       then
                         (do
                           let w__12 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                           (pure ((((_get_HCR_EL2_Type_E2H w__12) == 1#1) : Bool))))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__14 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
                      (pure ((((_get_TCR2_EL2_Type_D128 w__14) == 1#1) : Bool))))
                  else (pure false))
              else
                (do
                  if ((questionMark == EL3) : Bool)
                  then
                    (do
                      let w__16 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
                      let d128enabled := (((_get_TCR_EL3_Type_D128 w__16) == 1#1) : Bool)
                      (pure (d128enabled)))
                  else (pure (d128enabled))))))
  else (pure (false))


def GCSPCREnabled (el : (BitVec 2)) : SailM Bool := do
  if ((← do
       (GCSPCRSelected el)) : Bool)
  then
    (do
      (GCSEnabled el))
  else (pure false)


def CheckMOPSEnabled (_ : Unit) : SailM Unit := do
  let w__12 ← (( do
    if ((← do
         if ((← do
              if ((← do
                   if ((← do
                        let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__0.EL == EL0) : Bool)))) : Bool)
                   then (pure true)
                   else
                     (do
                       let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
                       (pure (((w__1.EL == EL1) : Bool))))) : Bool)
              then
                (do
                  (EL2Enabled ()))
              else (pure false)) : Bool)
         then
           (do
             if ((← do
                  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_TGE w__5) == 0#1) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                 (pure ((((_get_HCR_EL2_Type_E2H w__6) == 0#1) : Bool)))))
         else (pure false)) : Bool)
    then
      (do
        if ((← do
             let w__9 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
             (pure (((! w__9) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__10 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCRX_EL2_Type_MSCEn w__10) == 0#1) : Bool)))))
    else (pure false) ) : SailM Bool )
  if (w__12 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__21 ← (( do
    if ((← do
         if ((← do
              let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__13.EL == EL0) : Bool)))) : Bool)
         then
           (do
             let w__14 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
             (pure ((((_get_SCTLR_EL1_Type_MSCEn w__14) == 0#1) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        if ((← do
             if ((← do
                  let w__16 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  (pure (((! w__16) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                 (pure ((((_get_HCR_EL2_Type_TGE w__17) == 0#1) : Bool))))) : Bool)
        then (pure true)
        else
          (do
            let w__19 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_E2H w__19) == 0#1) : Bool)))))
    else (pure false) ) : SailM Bool )
  if (w__21 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__26 ← (( do
    if ((← do
         if ((← do
              let w__22 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__22.EL == EL0) : Bool)))) : Bool)
         then
           (do
             (IsInHost ()))
         else (pure false)) : Bool)
    then
      (do
        let w__25 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_SCTLR_EL2_Type_MSCEn w__25) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__26 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))


end ArmFull.Functions
