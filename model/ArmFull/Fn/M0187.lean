import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0011
import ArmFull.Fn.M0012
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0039
import ArmFull.Fn.M0040
import ArmFull.Fn.M0044
import ArmFull.Fn.M0047
import ArmFull.Fn.M0049
import ArmFull.Fn.M0097
import ArmFull.Fn.M0100
import ArmFull.Fn.M0112
import ArmFull.Fn.M0113
import ArmFull.Fn.M0115
import ArmFull.Fn.M0116
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0153
import ArmFull.Fn.M0154
import ArmFull.Fn.M0167
import ArmFull.Fn.M0171
import ArmFull.Fn.M0178
import ArmFull.Fn.M0179
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
import ArmFull.Fn.M0184
import ArmFull.Fn.M0185

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

/-- Type quantifiers: k_N : Nat, 4 < k_N -/
def IllegalExceptionReturn (spsr : (BitVec k_N)) : SailM Bool := SailME.run do
  let known ← (( do (undefined_bool_at (← occLabel 639) ()) ) : SailME Bool Bool )
  let target ← (( do (undefined_bitvector_at (← occLabel 640) 2) ) : SailME Bool (BitVec 2) )
  let target_el_is_aarch32 ← (( do (undefined_bool_at (← occLabel 641) ()) ) : SailME Bool Bool
    )
  let valid_name ← (( do (undefined_bool_at (← occLabel 642) ()) ) : SailME Bool Bool )
  let w__0 ← (( do (ELFromSPSR spsr) ) : SailME Bool (Bool × (BitVec 2)) )
  let (tup__0, tup__1) := (w__0 : (Bool × (BitVec 2)))
  let valid_name : Bool := tup__0
  let target : (BitVec 2) := tup__1
  if ((! valid_name) : Bool)
  then (pure (true))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailME Bool ProcState )
      if (((BitVec.toNat target) >b (BitVec.toNat w__1.EL)) : Bool)
      then (pure (true))
      else
        (do
          let spsr_mode_is_aarch32 : Bool :=
            ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spsr 4)])) == 1#1)
          let w__2 ← (( do (ELUsingAArch32K target) ) : SailME Bool (Bool × Bool) )
          let (tup__0, tup__1) := (w__2 : (Bool × Bool))
          let known : Bool := tup__0
          let target_el_is_aarch32 : Bool := tup__1
          let w__5 ← (( do
            if ((known : Bool) : Bool)
            then (pure true)
            else
              (do
                if (((target == EL0) : Bool) : Bool)
                then
                  (do
                    let w__3 ← (( do (ELUsingAArch32 EL1) ) : SailME Bool Bool )
                    (pure (((! w__3) : Bool))))
                else (pure false)) ) : SailME Bool Bool )
          ArmFull.assert w__5 "sail-arm/v8_base.sail:8252.64-8252.65"
          if ((known && (neq_bool spsr_mode_is_aarch32 target_el_is_aarch32)) : Bool)
          then (pure (true))
          else
            (do
              let w__7 ← (( do
                (pure ((← do
                      (UsingAArch32 ())) && (! spsr_mode_is_aarch32))) ) : SailME Bool Bool )
              if (w__7 : Bool)
              then (pure (true))
              else
                (do
                  let w__9 ← (( do
                    if ((((HaveEL EL2) && (target == EL1)) : Bool) : Bool)
                    then
                      (do
                        let w__8 ← (( do readReg HCR_EL2 ) : SailME Bool (BitVec 64) )
                        (pure ((((_get_HCR_EL2_Type_TGE w__8) == 1#1) : Bool))))
                    else (pure false) ) : SailME Bool Bool )
                  if (w__9 : Bool)
                  then
                    (do
                      let w__12 ← (( do
                        if ((← do
                             let w__10 ← (( do (IsSecureBelowEL3 ()) ) : SailME Bool Bool )
                             (pure (((! w__10) : Bool)))) : Bool)
                        then (pure true)
                        else
                          (do
                            (IsSecureEL2Enabled ())) ) : SailME Bool Bool )
                      if (w__12 : Bool)
                      then
                        (do
                          SailME.throw (true : Bool))
                      else (pure (())))
                  else (pure (()))
                  let w__21 ← (( do
                    if ((← do
                         if ((← do
                              if ((← do
                                   if ((← do
                                        (HaveGCS ())) : Bool)
                                   then
                                     (do
                                       let w__14 ← (( do readReg PSTATE ) : SailME Bool ProcState
                                         )
                                       (pure (((w__14.EXLOCK == 0#1) : Bool))))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  let w__16 ← (( do readReg PSTATE ) : SailME Bool ProcState )
                                  (pure (((w__16.EL == target) : Bool))))
                              else (pure false)) : Bool)
                         then
                           (do
                             (GetCurrentEXLOCKEN ()))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__20 ← (( do (Halted ()) ) : SailME Bool Bool )
                        (pure (((! w__20) : Bool))))
                    else (pure false) ) : SailME Bool Bool )
                  let w__22 : Bool :=
                    if (w__21 : Bool)
                    then true
                    else false
                  (pure (w__22))))))


def GCSEnabled (el : (BitVec 2)) : SailM Bool := do
  let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then (pure (false))
  else
    (do
      let w__2 ← (( do
        if ((((HaveEL EL3) && (el != EL3)) : Bool) : Bool)
        then
          (do
            let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            (pure ((((_get_SCR_EL3_Type_GCSEn w__1) == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__2 : Bool)
      then (pure (false))
      else
        (do
          let w__12 ← (( do
            if ((← do
                 if ((← do
                      if ((((el == EL0) || (el == EL1)) : Bool) : Bool)
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
                    (pure ((((_get_HCRX_EL2_Type_GCSEn w__10) == 0#1) : Bool)))))
            else (pure false) ) : SailM Bool )
          if (w__12 : Bool)
          then (pure (false))
          else
            (do
              (GCSPCRSelected el))))


def AltPIdRealm (el : (BitVec 2)) (primaryPIdSpace : PARTIDspaceType) : SailM PARTIDspaceType := do
  let PIdSpace : PARTIDspaceType := primaryPIdSpace
  let questionMark := el
  if ((questionMark == EL0) : Bool)
  then
    (do
      let w__0 ← (( do (ELIsInHost EL0) ) : SailM Bool )
      if (w__0 : Bool)
      then
        (do
          let w__1 ← (( do (UsePrimarySpaceEL2 ()) ) : SailM Bool )
          let PIdSpace : PARTIDspaceType :=
            if ((! w__1) : Bool)
            then PIdSpace_NonSecure
            else PIdSpace
          (pure (PIdSpace)))
      else
        (do
          let w__2 ← (( do (UsePrimarySpaceEL10 ()) ) : SailM Bool )
          let PIdSpace : PARTIDspaceType :=
            if ((! w__2) : Bool)
            then PIdSpace_NonSecure
            else PIdSpace
          (pure (PIdSpace))))
  else
    (do
      if ((questionMark == EL1) : Bool)
      then
        (do
          let w__3 ← (( do (UsePrimarySpaceEL10 ()) ) : SailM Bool )
          let PIdSpace : PARTIDspaceType :=
            if ((! w__3) : Bool)
            then PIdSpace_NonSecure
            else PIdSpace
          (pure (PIdSpace)))
      else
        (do
          if ((questionMark == EL2) : Bool)
          then
            (do
              let w__4 ← (( do (UsePrimarySpaceEL2 ()) ) : SailM Bool )
              let PIdSpace : PARTIDspaceType :=
                if ((! w__4) : Bool)
                then PIdSpace_NonSecure
                else PIdSpace
              (pure (PIdSpace)))
          else
            (do
              (Unreachable ())
              (pure (PIdSpace)))))


def AltPIdSecure (el : (BitVec 2)) (primaryPIdSpace : PARTIDspaceType) : SailM PARTIDspaceType := do
  let PIdSpace : PARTIDspaceType := primaryPIdSpace
  let el2en ← (( do (EL2Enabled ()) ) : SailM Bool )
  let questionMark := el
  if ((questionMark == EL0) : Bool)
  then
    (do
      if (el2en : Bool)
      then
        (do
          let w__0 ← (( do (ELIsInHost EL0) ) : SailM Bool )
          if (w__0 : Bool)
          then
            (do
              let w__1 ← (( do (UsePrimarySpaceEL2 ()) ) : SailM Bool )
              let PIdSpace : PARTIDspaceType :=
                if ((! w__1) : Bool)
                then PIdSpace_NonSecure
                else PIdSpace
              (pure (PIdSpace)))
          else
            (do
              let w__2 ← (( do (UsePrimarySpaceEL10 ()) ) : SailM Bool )
              let PIdSpace : PARTIDspaceType :=
                if ((! w__2) : Bool)
                then PIdSpace_NonSecure
                else PIdSpace
              (pure (PIdSpace))))
      else
        (do
          let w__5 ← (( do
            if ((← do
                 let w__3 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
                 (pure ((((_get_MPAM3_EL3_Type_ALTSP_HEN w__3) == 0#1) : Bool)))) : Bool)
            then
              (do
                let w__4 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
                (pure ((((_get_MPAM3_EL3_Type_ALTSP_HFC w__4) == 1#1) : Bool))))
            else (pure false) ) : SailM Bool )
          let PIdSpace : PARTIDspaceType :=
            if (w__5 : Bool)
            then PIdSpace_NonSecure
            else PIdSpace
          (pure (PIdSpace))))
  else
    (do
      if ((questionMark == EL1) : Bool)
      then
        (do
          if (el2en : Bool)
          then
            (do
              let w__6 ← (( do (UsePrimarySpaceEL10 ()) ) : SailM Bool )
              let PIdSpace : PARTIDspaceType :=
                if ((! w__6) : Bool)
                then PIdSpace_NonSecure
                else PIdSpace
              (pure (PIdSpace)))
          else
            (do
              let w__9 ← (( do
                if ((← do
                     let w__7 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
                     (pure ((((_get_MPAM3_EL3_Type_ALTSP_HEN w__7) == 0#1) : Bool)))) : Bool)
                then
                  (do
                    let w__8 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
                    (pure ((((_get_MPAM3_EL3_Type_ALTSP_HFC w__8) == 1#1) : Bool))))
                else (pure false) ) : SailM Bool )
              let PIdSpace : PARTIDspaceType :=
                if (w__9 : Bool)
                then PIdSpace_NonSecure
                else PIdSpace
              (pure (PIdSpace))))
      else
        (do
          if ((questionMark == EL2) : Bool)
          then
            (do
              let w__10 ← (( do (UsePrimarySpaceEL2 ()) ) : SailM Bool )
              let PIdSpace : PARTIDspaceType :=
                if ((! w__10) : Bool)
                then PIdSpace_NonSecure
                else PIdSpace
              (pure (PIdSpace)))
          else
            (do
              (Unreachable ())
              (pure (PIdSpace)))))


/-- Type quantifiers: k_InD : Bool, k_InSM : Bool -/
def genPARTID (el : (BitVec 2)) (InD : Bool) (InSM : Bool) : SailM ((BitVec 16) × Bool) := do
  let partidel ← (( do (getMPAM_PARTID el InD InSM) ) : SailM PARTIDtype )
  let w__0 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
  let partid_max : PARTIDtype := (_get_MPAMIDR_EL1_Type_PARTID_MAX w__0)
  if (((BitVec.toNat partidel) >b (BitVec.toNat partid_max)) : Bool)
  then (pure ((DefaultPARTID, true)))
  else
    (do
      let w__1 ← (( do (MPAMisVirtual el) ) : SailM Bool )
      if (w__1 : Bool)
      then
        (do
          (MAP_vPARTID partidel))
      else (pure ((partidel, false))))


/-- Type quantifiers: k_InD : Bool, k_InSM : Bool, k_partid_err : Bool -/
def genPMG (el : (BitVec 2)) (InD : Bool) (InSM : Bool) (partid_err : Bool) : SailM (BitVec 8) := do
  let w__0 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
  let pmg_max : Int := (BitVec.toNat (_get_MPAMIDR_EL1_Type_PMG_MAX w__0))
  if (partid_err : Bool)
  then (pure (DefaultPMG))
  else
    (do
      let groupel ← (( do (getMPAM_PMG el InD InSM) ) : SailM PMGtype )
      (pure (if (((BitVec.toNat groupel) ≤b pmg_max) : Bool)
        then groupel
        else DefaultPMG)))


def TargetSecurityState (NS : (BitVec 1)) (NSE : (BitVec 1)) : SailM SecurityState := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let curr_ss ← (( do (SecurityStateAtEL w__0.EL) ) : SailM SecurityState )
  if ((BEq.beq curr_ss SS_NonSecure) : Bool)
  then (pure (SS_NonSecure))
  else
    (do
      if ((BEq.beq curr_ss SS_Secure) : Bool)
      then
        (do
          match NS with
          | 0 => (pure (SS_Secure))
          | 1 => (pure (SS_NonSecure))
          | _ =>
            (do
              (undefined_SecurityState (← occLabel 796) ())))
      else
        (do
          let w__3 ← (( do (HaveRME ()) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              if ((BEq.beq curr_ss SS_Root) : Bool)
              then
                (do
                  match (BitVec.setWidth 2 (NSE +++ NS)) with
                  | 0b00 => (pure (SS_Secure))
                  | 0b01 => (pure (SS_NonSecure))
                  | 0b11 => (pure (SS_Realm))
                  | 0b10 => (pure (SS_Root))
                  | _ =>
                    (do
                      (undefined_SecurityState (← occLabel 795) ())))
              else
                (do
                  if ((BEq.beq curr_ss SS_Realm) : Bool)
                  then (pure (SS_Realm))
                  else
                    (do
                      (undefined_SecurityState (← occLabel 794) ()))))
          else
            (do
              (undefined_SecurityState (← occLabel 793) ()))))


def AArch64_PEErrorState (fault : FaultRecord) : SailM ErrorState := SailME.run do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (IsExternalSyncAbort__1 fault) ) : SailME ErrorState Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        (ExtAbortToA64 fault))
    else (pure false) ) : SailME ErrorState Bool )
  if (w__2 : Bool)
  then
    (do
      let w__3 ← (( do (ReportErrorAsUncategorized ()) ) : SailME ErrorState Bool )
      if (w__3 : Bool)
      then
        (do
          SailME.throw (ErrorState_Uncategorized : ErrorState))
      else
        (do
          let w__4 ← (( do (ReportErrorAsIMPDEF ()) ) : SailME ErrorState Bool )
          if (w__4 : Bool)
          then
            (do
              SailME.throw (ErrorState_IMPDEF : ErrorState))
          else (pure (()))))
  else (pure (()))
  let w__5 ← (( do (FaultIsCorrected ()) ) : SailME ErrorState Bool )
  ArmFull.assert (! w__5) "sail-arm/v8_base.sail:14707.39-14707.40"
  let w__12 ← (( do
    if ((← do
         if ((← do
              let w__6 ← (( do (ErrorIsContained ()) ) : SailME ErrorState Bool )
              (pure (((! w__6) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             if ((← do
                  let w__7 ← (( do (ErrorIsSynchronized ()) ) : SailME ErrorState Bool )
                  (pure (((! w__7) : Bool)))) : Bool)
             then
               (do
                 let w__8 ← (( do (StateIsRecoverable ()) ) : SailME ErrorState Bool )
                 (pure (((! w__8) : Bool))))
             else (pure false))) : Bool)
    then (pure true)
    else
      (do
        (ReportErrorAsUC ())) ) : SailME ErrorState Bool )
  if (w__12 : Bool)
  then (pure (ErrorState_UC))
  else
    (do
      let w__15 ← (( do
        if ((← do
             let w__13 ← (( do (StateIsRecoverable ()) ) : SailME ErrorState Bool )
             (pure (((! w__13) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            (ReportErrorAsUEU ())) ) : SailME ErrorState Bool )
      if (w__15 : Bool)
      then
        (do
          let w__16 ← (( do (IsExternalSyncAbort__1 fault) ) : SailME ErrorState Bool )
          let w__17 : ErrorState :=
            if (w__16 : Bool)
            then ErrorState_UC
            else ErrorState_UEU
          (pure (w__17)))
      else
        (do
          let w__20 ← (( do
            if ((← do
                 (ActionRequired ())) : Bool)
            then (pure true)
            else
              (do
                (ReportErrorAsUER ())) ) : SailME ErrorState Bool )
          let w__21 : ErrorState :=
            if (w__20 : Bool)
            then ErrorState_UER
            else ErrorState_UEO
          (pure (w__21))))


def IsSCTLR2EL1Enabled (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (HaveFeatSCTLR2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let w__2 ← (( do
        if (((HaveEL EL3) : Bool) : Bool)
        then
          (do
            let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            (pure ((((_get_SCR_EL3_Type_SCTLR2En w__1) == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__2 : Bool)
      then (pure (false))
      else
        (do
          let w__7 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                if ((← do
                     let w__4 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                     (pure (((! w__4) : Bool)))) : Bool)
                then (pure true)
                else
                  (do
                    let w__5 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
                    (pure ((((_get_HCRX_EL2_Type_SCTLR2En w__5) == 0#1) : Bool)))))
            else (pure false) ) : SailM Bool )
          let w__8 : Bool :=
            if (w__7 : Bool)
            then false
            else true
          (pure (w__8))))


def SecurityStateForRegime (regime : Regime) : SailM SecurityState := do
  match regime with
  | .Regime_EL3 =>
    (do
      (SecurityStateAtEL EL3))
  | .Regime_EL30 => (pure (SS_Secure))
  | .Regime_EL2 =>
    (do
      (SecurityStateAtEL EL2))
  | .Regime_EL20 =>
    (do
      (SecurityStateAtEL EL2))
  | .Regime_EL10 =>
    (do
      (SecurityStateAtEL EL1))


def IsTCR2EL1Enabled (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (HaveFeatTCR2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let w__2 ← (( do
        if (((HaveEL EL3) : Bool) : Bool)
        then
          (do
            let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            (pure ((((_get_SCR_EL3_Type_TCR2En w__1) == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__2 : Bool)
      then (pure (false))
      else
        (do
          let w__7 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                if ((← do
                     let w__4 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                     (pure (((! w__4) : Bool)))) : Bool)
                then (pure true)
                else
                  (do
                    let w__5 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
                    (pure ((((_get_HCRX_EL2_Type_TCR2En w__5) == 0#1) : Bool)))))
            else (pure false) ) : SailM Bool )
          let w__8 : Bool :=
            if (w__7 : Bool)
            then false
            else true
          (pure (w__8))))


def AArch64_S1TTWParamsEL2 (ss : SecurityState) : SailM S1TTWParams := do
  let walkparams ← (( do (undefined_S1TTWParams (← occLabel 1265) ()) ) : SailM S1TTWParams )
  let w__0 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  let w__1 ← (( do (AArch64_S1DecodeTG0 (_get_TCR_EL2_Type_TG0 w__0)) ) : SailM TGx )
  let walkparams := ({ walkparams with tgx := w__1 } : S1TTWParams)
  let w__2 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with txsz := (_get_TCR_EL2_Type_T0SZ w__2) } : S1TTWParams)
  let w__3 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with ps := (_get_TCR_EL2_Type_PS w__3) } : S1TTWParams)
  let w__4 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with irgn := (_get_TCR_EL2_Type_IRGN0 w__4) } : S1TTWParams)
  let w__5 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with orgn := (_get_TCR_EL2_Type_ORGN0 w__5) } : S1TTWParams)
  let w__6 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with sh := (_get_TCR_EL2_Type_SH0 w__6) } : S1TTWParams)
  let w__7 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with tbi := (_get_TCR_EL2_Type_TBI w__7) } : S1TTWParams)
  let w__8 ← (( do readReg MAIR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with mair := (Mk_MAIRType w__8) } : S1TTWParams)
  let w__9 ← (( do (HaveAIEExt ()) ) : SailM Bool )
  let walkparams ← (( do
    if (w__9 : Bool)
    then
      (do
        let w__10 ← (( do readReg MAIR2_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with mair2 := (Mk_MAIRType w__10) } : S1TTWParams)
        (pure (walkparams)))
    else (pure (walkparams)) ) : SailM S1TTWParams )
  let w__13 ← (( do
    if ((← do
         (HaveAIEExt ())) : Bool)
    then
      (do
        (IsTCR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let w__15 ← (( do
    if (w__13 : Bool)
    then
      (do
        let w__14 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_TCR2_EL2_Type_AIE w__14))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with aie := w__15 } : S1TTWParams)
  let w__16 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with wxn := (_get_SCTLR_EL2_Type_WXN w__16) } : S1TTWParams)
  let w__17 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with ee := (_get_SCTLR_EL2_Type_EE w__17) } : S1TTWParams)
  let w__21 ← (( do
    if (((HaveEL EL3) : Bool) : Bool)
    then
      (do
        if ((← do
             let w__18 ← (( do (HaveRME ()) ) : SailM Bool )
             (pure (((! w__18) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            (HaveSecureEL2Ext ())))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__21 : Bool)
    then
      (do
        let w__22 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with sif := (_get_SCR_EL3_Type_SIF w__22) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with sif := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__23 ← (( do (HavePACExt ()) ) : SailM Bool )
  let w__25 ← (( do
    if (w__23 : Bool)
    then
      (do
        let w__24 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL2_Type_TBID w__24))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with tbid := w__25 } : S1TTWParams)
  let w__26 ← (( do (AArch64_HaveHPDExt ()) ) : SailM Bool )
  let w__28 ← (( do
    if (w__26 : Bool)
    then
      (do
        let w__27 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL2_Type_HPD w__27))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with hpd := w__28 } : S1TTWParams)
  let w__29 ← (( do (HaveAccessFlagUpdateExt ()) ) : SailM Bool )
  let w__33 ← (( do
    if (w__29 : Bool)
    then
      (do
        let w__30 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let w__31 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let w__32 : Int :=
          if (((_get_HCR_EL2_Type_E2H w__31) == 0#1) : Bool)
          then 21
          else 39
        (pure ((BitVec.slice w__30 (Sail.Int.toNatChecked (w__32)) 1))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with ha := w__33 } : S1TTWParams)
  let w__34 ← (( do (HaveDirtyBitModifierExt ()) ) : SailM Bool )
  let w__38 ← (( do
    if (w__34 : Bool)
    then
      (do
        let w__35 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let w__36 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let w__37 : Int :=
          if (((_get_HCR_EL2_Type_E2H w__36) == 0#1) : Bool)
          then 22
          else 40
        (pure ((BitVec.slice w__35 (Sail.Int.toNatChecked (w__37)) 1))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with hd := w__38 } : S1TTWParams)
  let w__40 ← (( do
    if ((((BEq.beq walkparams.tgx TGx_4KB) || (BEq.beq walkparams.tgx TGx_16KB)) : Bool) : Bool)
    then
      (do
        (Have52BitIPAAndPASpaceExt ()))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__40 : Bool)
    then
      (do
        let w__41 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        let w__42 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let w__43 : Int :=
          if (((_get_HCR_EL2_Type_E2H w__42) == 0#1) : Bool)
          then 32
          else 59
        let walkparams :=
          ({ walkparams with ds := (BitVec.slice w__41 (Sail.Int.toNatChecked (w__43)) 1) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with ds := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__46 ← (( do
    if ((← do
         (HaveS1PIExt ())) : Bool)
    then
      (do
        (IsTCR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let w__48 ← (( do
    if (w__46 : Bool)
    then
      (do
        let w__47 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_TCR2_EL2_Type_PIE w__47))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with pie := w__48 } : S1TTWParams)
  let w__49 ← (( do (HaveS1PIExt ()) ) : SailM Bool )
  let walkparams ← (( do
    if (w__49 : Bool)
    then
      (do
        let w__50 ← (( do readReg PIR_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with pir := (Mk_S1PIRType w__50) } : S1TTWParams)
        (pure (walkparams)))
    else (pure (walkparams)) ) : SailM S1TTWParams )
  let w__51 ← (( do (HaveMTE4Ext ()) ) : SailM Bool )
  let w__53 ← (( do
    if (w__51 : Bool)
    then
      (do
        let w__52 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL2_Type_MTX w__52))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with mtx := w__53 } : S1TTWParams)
  let w__56 ← (( do
    if ((← do
         (HaveTHExt ())) : Bool)
    then
      (do
        (IsTCR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let w__58 ← (( do
    if (w__56 : Bool)
    then
      (do
        let w__57 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_TCR2_EL2_Type_PnCH w__57))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with pnch := w__58 } : S1TTWParams)
  let w__62 ← (( do
    if ((← do
         (pure ((← do
               (HaveAccessFlagUpdateForTableExt ())) && ((walkparams.ha == 1#1) : Bool)))) : Bool)
    then
      (do
        (IsTCR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__62 : Bool)
    then
      (do
        let w__63 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with haft := (_get_TCR2_EL2_Type_HAFT w__63) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with haft := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__66 ← (( do
    if ((← do
         (HaveFeatMEC ())) : Bool)
    then
      (do
        (IsSCTLR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let w__68 ← (( do
    if (w__66 : Bool)
    then
      (do
        let w__67 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_SCTLR2_EL2_Type_EMEC w__67))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with emec := w__68 } : S1TTWParams)
  let w__72 ← (( do
    if ((← do
         (pure ((← do
               (HaveFeatMEC ())) && ((BEq.beq ss SS_Realm) : Bool)))) : Bool)
    then
      (do
        (IsTCR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  if (w__72 : Bool)
  then
    (do
      let w__73 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let walkparams := ({ walkparams with amec := (_get_TCR2_EL2_Type_AMEC0 w__73) } : S1TTWParams)
      (pure (walkparams)))
  else
    (let walkparams : S1TTWParams := { walkparams with amec := 0#1 }
    (pure (walkparams)))


end ArmFull.Functions
