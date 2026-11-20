module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0040
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0112
public import ArmFull.Fn.M0113
public import ArmFull.Fn.M0115
public import ArmFull.Fn.M0116
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0151
public import ArmFull.Fn.M0152
public import ArmFull.Fn.M0171
public import ArmFull.Fn.M0173
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0179
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0183 set_option backward.proofsInPublic true @[expose] public section

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

def PMUCounterMask (_ : Unit) : SailM (BitVec 64) := do
  let n ← (( do (undefined_int_at (← occLabel 502) ()) ) : SailM Int )
  let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  let n ← (( do
    if (w__0 : Bool)
    then
      (do
        (AArch32_GetNumEventCountersAccessible ()))
    else
      (do
        (AArch64_GetNumEventCountersAccessible ())) ) : SailM Int )
  let n : Int := n
  ArmFull.assert (n ≥b 0) "sail-inputs/03-v8_base.sail:4047.30-4047.31"
  ArmFull.assert (64 ≥b n) "sail-inputs/03-v8_base.sail:4048.31-4048.32"
  let mask : (BitVec 64) := (Sail.BitVec.zeroExtend (Ones (n := (Sail.Int.toNatChecked (n)))) 64)
  let mask : (BitVec 64) := (BitVec.update mask CYCLE_COUNTER_ID (Bit 1#1))
  let w__5 ← (( do
    if ((← do
         (HaveAArch64 ())) : Bool)
    then
      (do
        (HavePMUv3ICNTR ()))
    else (pure false) ) : SailM Bool )
  let mask : (BitVec 64) :=
    if (w__5 : Bool)
    then (BitVec.update mask INSTRUCTION_COUNTER_ID (Bit 1#1))
    else mask
  (pure (mask))


def CurrentSecurityState (_ : Unit) : SailM SecurityState := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  (SecurityStateAtEL w__0.EL)


def S1TranslationRegime (el : (BitVec 2)) : SailM (BitVec 2) := do
  if ((el != EL0) : Bool)
  then (pure (el))
  else
    (do
      let w__4 ← (( do
        if ((← do
             if ((← do
                  (HaveEL EL3)) : Bool)
             then
               (do
                 (ELUsingAArch32 EL3))
             else (pure false)) : Bool)
        then
          (do
            let w__3 ← (( do readReg SCR ) : SailM (BitVec 32) )
            (pure ((((_get_SCR_Type_NS w__3) == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then (pure (EL3))
      else
        (do
          let w__7 ← (( do
            if ((← do
                 (HaveVirtHostExt ())) : Bool)
            then
              (do
                (ELIsInHost el))
            else (pure false) ) : SailM Bool )
          let w__8 : (BitVec 2) :=
            if (w__7 : Bool)
            then EL2
            else EL1
          (pure (w__8))))


def IsInHost (_ : Unit) : SailM Bool := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  (ELIsInHost w__0.EL)


def StatisticalProfilingEnabled__1 (el : (BitVec 2)) : SailM Bool := do
  let owning_el ← (( do (undefined_bitvector_at (← occLabel 590) 2) ) : SailM (BitVec 2) )
  let owning_ss ← (( do (undefined_SecurityState (← occLabel 591) ()) ) : SailM SecurityState )
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do (HaveStatisticalProfiling ()) ) : SailM Bool )
              (pure (((! w__0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             (UsingAArch32 ()))) : Bool)
    then (pure true)
    else
      (do
        let w__3 ← (( do (ProfilingBufferEnabled ()) ) : SailM Bool )
        (pure (((! w__3) : Bool)))) ) : SailM Bool )
  if (w__4 : Bool)
  then (pure (false))
  else
    (do
      let tge_set ← (( do
        if ((← do
             (EL2Enabled ())) : Bool)
        then
          (do
            let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_TGE w__6) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      let w__7 ← (( do (ProfilingBufferOwner ()) ) : SailM (SecurityState × (BitVec 2)) )
      let (tup__0, tup__1) := (w__7 : (SecurityState × (BitVec 2)))
      let owning_ss : SecurityState := tup__0
      let owning_el : (BitVec 2) := tup__1
      let w__9 ← (( do
        if ((((BitVec.toNat owning_el) <b (BitVec.toNat el)) || (tge_set && (owning_el == EL1))) : Bool)
        then (pure true)
        else
          (do
            let w__8 ← (( do (SecurityStateAtEL el) ) : SailM SecurityState )
            (pure (((bne owning_ss w__8) : Bool)))) ) : SailM Bool )
      if (w__9 : Bool)
      then (pure (false))
      else
        (do
          let spe_bit ← (( do (undefined_bitvector_at (← occLabel 592) 1) ) : SailM (BitVec 1) )
          let questionMark := el
          let spe_bit ← (( do
            if ((questionMark == EL3) : Bool)
            then
              (do
                (Unreachable ())
                (pure (spe_bit)))
            else
              (do
                if ((questionMark == EL2) : Bool)
                then
                  (do
                    let w__10 ← (( do readReg PMSCR_EL2 ) : SailM (BitVec 64) )
                    let spe_bit := ((_get_PMSCR_EL2_Type_E2SPE w__10) : (BitVec 1))
                    (pure (spe_bit)))
                else
                  (do
                    if ((questionMark == EL1) : Bool)
                    then
                      (do
                        let w__11 ← (( do readReg PMSCR_EL1 ) : SailM (BitVec 64) )
                        let spe_bit := ((_get_PMSCR_EL1_Type_E1SPE w__11) : (BitVec 1))
                        (pure (spe_bit)))
                    else
                      (do
                        if ((questionMark == EL0) : Bool)
                        then
                          (do
                            if (tge_set : Bool)
                            then
                              (do
                                let w__12 ← (( do readReg PMSCR_EL2 ) : SailM (BitVec 64) )
                                (pure ((_get_PMSCR_EL2_Type_E0HSPE w__12))))
                            else
                              (do
                                let w__13 ← (( do readReg PMSCR_EL1 ) : SailM (BitVec 64) )
                                (pure ((_get_PMSCR_EL1_Type_E0SPE w__13)))))
                        else (pure (spe_bit))))) ) : SailM (BitVec 1) )
          (pure ((spe_bit == 1#1)))))


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
          ArmFull.assert w__5 "sail-inputs/03-v8_base.sail:8259.64-8259.65"
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
                  let w__11 ← (( do
                    if ((← do
                         (pure ((← do
                               (HaveEL EL2)) && ((target == EL1) : Bool)))) : Bool)
                    then
                      (do
                        let w__10 ← (( do readReg HCR_EL2 ) : SailME Bool (BitVec 64) )
                        (pure ((((_get_HCR_EL2_Type_TGE w__10) == 1#1) : Bool))))
                    else (pure false) ) : SailME Bool Bool )
                  if (w__11 : Bool)
                  then
                    (do
                      let w__14 ← (( do
                        if ((← do
                             let w__12 ← (( do (IsSecureBelowEL3 ()) ) : SailME Bool Bool )
                             (pure (((! w__12) : Bool)))) : Bool)
                        then (pure true)
                        else
                          (do
                            (IsSecureEL2Enabled ())) ) : SailME Bool Bool )
                      if (w__14 : Bool)
                      then
                        (do
                          SailME.throw (true : Bool))
                      else (pure (())))
                  else (pure (()))
                  let w__23 ← (( do
                    if ((← do
                         if ((← do
                              if ((← do
                                   if ((← do
                                        (HaveGCS ())) : Bool)
                                   then
                                     (do
                                       let w__16 ← (( do readReg PSTATE ) : SailME Bool ProcState
                                         )
                                       (pure (((w__16.EXLOCK == 0#1) : Bool))))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  let w__18 ← (( do readReg PSTATE ) : SailME Bool ProcState )
                                  (pure (((w__18.EL == target) : Bool))))
                              else (pure false)) : Bool)
                         then
                           (do
                             (GetCurrentEXLOCKEN ()))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__22 ← (( do (Halted ()) ) : SailME Bool Bool )
                        (pure (((! w__22) : Bool))))
                    else (pure false) ) : SailME Bool Bool )
                  let w__24 : Bool :=
                    if (w__23 : Bool)
                    then true
                    else false
                  (pure (w__24))))))


def GCSEnabled (el : (BitVec 2)) : SailM Bool := do
  let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then (pure (false))
  else
    (do
      let w__4 ← (( do
        if ((← do
             (pure ((← do
                   (HaveEL EL3)) && ((el != EL3) : Bool)))) : Bool)
        then
          (do
            let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            (pure ((((_get_SCR_EL3_Type_GCSEn w__3) == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then (pure (false))
      else
        (do
          let w__14 ← (( do
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
                          let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure ((((_get_HCR_EL2_Type_TGE w__7) == 0#1) : Bool)))) : Bool)
                     then (pure true)
                     else
                       (do
                         let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                         (pure ((((_get_HCR_EL2_Type_E2H w__8) == 0#1) : Bool)))))
                 else (pure false)) : Bool)
            then
              (do
                if ((← do
                     let w__11 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                     (pure (((! w__11) : Bool)))) : Bool)
                then (pure true)
                else
                  (do
                    let w__12 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
                    (pure ((((_get_HCRX_EL2_Type_GCSEn w__12) == 0#1) : Bool)))))
            else (pure false) ) : SailM Bool )
          if (w__14 : Bool)
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
  ArmFull.assert (! w__5) "sail-inputs/03-v8_base.sail:14720.39-14720.40"
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


end ArmFull.Functions
