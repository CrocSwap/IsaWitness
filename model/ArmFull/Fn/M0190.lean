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
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0152
public import ArmFull.Fn.M0167
public import ArmFull.Fn.M0171
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0179
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0183
public import ArmFull.Fn.M0184 set_option backward.proofsInPublic true @[expose] public section

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

def AArch64_GetS2TLBContext (ss : SecurityState) (ipa : FullAddress) (tg : TGx) : SailM TLBContext := do
  let w__0 ← (( do (EL2Enabled ()) ) : SailM Bool )
  ArmFull.assert w__0 "sail-inputs/03-v8_base.sail:26622.23-26622.24"
  let tlbcontext ← (( do (undefined_TLBContext (← occLabel 1551) ()) ) : SailM TLBContext )
  let tlbcontext : TLBContext := { tlbcontext with ss := ss }
  let tlbcontext : TLBContext := { tlbcontext with regime := Regime_EL10 }
  let tlbcontext : TLBContext := { tlbcontext with ipaspace := ipa.paspace }
  let w__1 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
  let tlbcontext := ({ tlbcontext with vmid := w__1 } : TLBContext)
  let tlbcontext : TLBContext := { tlbcontext with tg := tg }
  let tlbcontext : TLBContext := { tlbcontext with ia := (Sail.BitVec.zeroExtend ipa.address 64) }
  let w__2 ← (( do (HaveCommonNotPrivateTransExt ()) ) : SailM Bool )
  let tlbcontext ← (( do
    if (w__2 : Bool)
    then
      (do
        let w__5 ← (( do
          if ((BEq.beq ipa.paspace PAS_Secure) : Bool)
          then
            (do
              let w__3 ← (( do readReg VSTTBR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_VSTTBR_EL2_Type_CnP w__3))))
          else
            (do
              let w__4 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
              (pure ((_get_VTTBR_EL2_Type_CnP w__4)))) ) : SailM (BitVec 1) )
        let tlbcontext := ({ tlbcontext with cnp := w__5 } : TLBContext)
        (pure (tlbcontext)))
    else
      (let tlbcontext : TLBContext := { tlbcontext with cnp := 0#1 }
      (pure (tlbcontext))) ) : SailM TLBContext )
  let tlbcontext : TLBContext := { tlbcontext with includes_s1_name := false }
  let tlbcontext : TLBContext := { tlbcontext with includes_s2_name := true }
  let tlbcontext : TLBContext := { tlbcontext with includes_gpt_name := false }
  (pure (tlbcontext))


def MismatchedCpySetTargetEL (_ : Unit) : SailM (BitVec 2) := do
  let target_el ← (( do (undefined_bitvector_at (← occLabel 1763) 2) ) : SailM (BitVec 2) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if (((BitVec.toNat w__0.EL) >b (BitVec.toNat EL1)) : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let target_el := (w__1.EL : (BitVec 2))
      (pure (target_el)))
  else
    (do
      let w__6 ← (( do
        if ((← do
             if ((← do
                  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__2.EL == EL0) : Bool)))) : Bool)
             then
               (do
                 (EL2Enabled ()))
             else (pure false)) : Bool)
        then
          (do
            let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_TGE w__5) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__6 : Bool)
      then (pure (EL2))
      else
        (do
          let w__13 ← (( do
            if ((← do
                 if ((← do
                      if ((← do
                           let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
                           (pure (((w__7.EL == EL1) : Bool)))) : Bool)
                      then
                        (do
                          (EL2Enabled ()))
                      else (pure false)) : Bool)
                 then
                   (do
                     (IsHCRXEL2Enabled ()))
                 else (pure false)) : Bool)
            then
              (do
                let w__12 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_HCRX_EL2_Type_MCE2 w__12) == 1#1) : Bool))))
            else (pure false) ) : SailM Bool )
          let target_el : (BitVec 2) :=
            if (w__13 : Bool)
            then EL2
            else EL1
          (pure (target_el))))


def ExternalDebugInterruptsDisabled (target : (BitVec 2)) : SailM Bool := do
  let int_dis ← (( do (undefined_bool_at (← occLabel 1929) ()) ) : SailM Bool )
  let ss ← (( do (SecurityStateAtEL target) ) : SailM SecurityState )
  let w__0 ← (( do (Havev8p4Debug ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access (_get_EDSCR_Type_INTdis w__1) 0)])) == 1#1) : Bool)
      then
        (do
          match ss with
          | .SS_NonSecure =>
            (do
              (ExternalInvasiveDebugEnabled ()))
          | .SS_Secure =>
            (do
              (ExternalSecureInvasiveDebugEnabled ()))
          | .SS_Realm =>
            (do
              (ExternalRealmInvasiveDebugEnabled ()))
          | .SS_Root =>
            (do
              (ExternalRootInvasiveDebugEnabled ())))
      else (pure (false)))
  else
    (do
      let questionMark := target
      if ((questionMark == EL3) : Bool)
      then
        (do
          if ((← do
               let w__6 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
               (pure ((((_get_EDSCR_Type_INTdis w__6) == 0b11#2) : Bool)))) : Bool)
          then
            (do
              (ExternalSecureInvasiveDebugEnabled ()))
          else (pure false))
      else
        (do
          if ((questionMark == EL2) : Bool)
          then
            (do
              if ((← do
                   let w__9 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                   let b__0 := (_get_EDSCR_Type_INTdis w__9)
                   (pure ((if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 1 1)) == (1#1 : (BitVec 1))) : Bool)
                     then true
                     else false : Bool)))) : Bool)
              then
                (do
                  (ExternalInvasiveDebugEnabled ()))
              else (pure false))
          else
            (do
              if ((questionMark == EL1) : Bool)
              then
                (do
                  if ((BEq.beq ss SS_Secure) : Bool)
                  then
                    (do
                      if ((← do
                           let w__12 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                           let b__1 := (_get_EDSCR_Type_INTdis w__12)
                           (pure ((if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1
                                    1 1)) == (1#1 : (BitVec 1))) : Bool)
                             then true
                             else false : Bool)))) : Bool)
                      then
                        (do
                          (ExternalSecureInvasiveDebugEnabled ()))
                      else (pure false))
                  else
                    (do
                      if ((← do
                           let w__15 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                           (pure ((((_get_EDSCR_Type_INTdis w__15) != 0b00#2) : Bool)))) : Bool)
                      then
                        (do
                          (ExternalInvasiveDebugEnabled ()))
                      else (pure false)))
              else (pure (int_dis)))))


def AArch64_ClearEventCounters (_ : Unit) : SailM Unit := do
  let counters ← (( do (AArch64_GetNumEventCountersAccessible ()) ) : SailM Int )
  if ((counters != 0) : Bool)
  then
    (do
      let loop_idx_lower : Nat := 0
      let loop_idx_upper : Int := (counters -i 1)
      (do
        let mut loop_vars := ()
        for idx in [loop_idx_lower:loop_idx_upper:1]i do
          let () := loop_vars
          loop_vars ← do
            ArmFull.assert ((0 ≤b idx) && (idx <b 32)) "sail-inputs/03-v8_base.sail:34407.64-34407.65"
            let w__0 ← (( do readReg PMEVCNTR_EL0 ) : SailM (Vector (BitVec 64) 32) )
            writeReg PMEVCNTR_EL0 (vectorUpdate w__0 (Sail.Int.toNatChecked (idx)) (Zeros (n := 64)))
        (pure loop_vars)))
  else (pure (()))


def AArch64_PMUSwIncrement (sw_incr : (BitVec 32)) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
         (pure ((((_get_PMCR_EL0_Type_E w__0) == 0#1) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_MDCR_EL2_Type_HPME w__1) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then (pure (()))
  else
    (do
      let counters ← (( do (AArch64_GetNumEventCountersAccessible ()) ) : SailM Int )
      if ((counters != 0) : Bool)
      then
        (do
          let loop_idx_lower : Nat := 0
          let loop_idx_upper : Int := (counters -i 1)
          (do
            let mut loop_vars := ()
            for idx in [loop_idx_lower:loop_idx_upper:1]i do
              let () := loop_vars
              loop_vars ← do
                ArmFull.assert ((0 ≤b idx) && (idx <b 32)) "sail-inputs/03-v8_base.sail:34423.64-34423.65"
                if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access sw_incr
                         (Sail.Int.toNatChecked (idx)))])) == 1#1) : Bool)
                then
                  (do
                    (PMUEvent__2 PMU_EVENT_SW_INCR 1 idx))
                else (pure (()))
            (pure loop_vars)))
      else (pure (())))


def AArch32_WriteModeByInstr (mode : (BitVec 5)) : SailM Unit := do
  let el ← (( do (undefined_bitvector_at (← occLabel 2766) 2) ) : SailM (BitVec 2) )
  let valid_name ← (( do (undefined_bool_at (← occLabel 2767) ()) ) : SailM Bool )
  let w__0 ← (( do (ELFromM32 mode) ) : SailM (Bool × (BitVec 2)) )
  let (tup__0, tup__1) := (w__0 : (Bool × (BitVec 2)))
  let valid_name : Bool := tup__0
  let el : (BitVec 2) := tup__1
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let valid_name : Bool :=
    if (((BitVec.toNat el) >b (BitVec.toNat w__1.EL)) : Bool)
    then false
    else valid_name
  let w__5 ← (( do
    if ((← do
         (pure ((← do
               let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
               (pure (((w__2.M == M32_Hyp) : Bool)))) || ((mode == M32_Hyp) : Bool)))) : Bool)
    then
      (do
        let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__4.M != mode) : Bool))))
    else (pure false) ) : SailM Bool )
  let valid_name : Bool :=
    if (w__5 : Bool)
    then false
    else valid_name
  let w__13 ← (( do
    if ((← do
         if ((← do
              (pure ((← do
                    if ((← do
                         let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
                         (pure (((w__6.M == M32_Monitor) : Bool)))) : Bool)
                    then
                      (do
                        (HaveEL EL2))
                    else (pure false)) && ((el == EL1) : Bool)))) : Bool)
         then
           (do
             let w__10 ← (( do readReg SCR ) : SailM (BitVec 32) )
             (pure ((((_get_SCR_Type_NS w__10) == 1#1) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__12 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
        (pure ((((_get_HCR_Type_TGE w__12) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let valid_name : Bool :=
    if (w__13 : Bool)
    then false
    else valid_name
  let valid_name := valid_name
  if ((! valid_name) : Bool)
  then
    (do
      let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__14 with IL := 1#1 })
  else
    (do
      (AArch32_WriteMode mode))


def AArch32_PMUSwIncrement (sw_incr : (BitVec 32)) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
         (pure ((((_get_PMCR_Type_E w__0) == 0#1) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
        (pure ((((_get_HDCR_Type_HPME w__1) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then (pure (()))
  else
    (do
      let counters ← (( do (AArch32_GetNumEventCountersAccessible ()) ) : SailM Int )
      if ((counters != 0) : Bool)
      then
        (do
          let loop_idx_lower : Nat := 0
          let loop_idx_upper : Int := (counters -i 1)
          (do
            let mut loop_vars := ()
            for idx in [loop_idx_lower:loop_idx_upper:1]i do
              let () := loop_vars
              loop_vars ← do
                ArmFull.assert ((0 ≤b idx) && (idx <b 32)) "sail-inputs/03-v8_base.sail:43539.64-43539.65"
                if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access sw_incr
                         (Sail.Int.toNatChecked (idx)))])) == 1#1) : Bool)
                then
                  (do
                    (PMUEvent__2 PMU_EVENT_SW_INCR 1 idx))
                else (pure (()))
            (pure loop_vars)))
      else (pure (())))


/-- Type quantifiers: t : Int -/
def TLBI_ALLE3IS_SysOpsWrite_95e13b1ef487429e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__2 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                      (AArch64_TLBI_ALL w__2 Regime_EL3 Shareability_ISH TLBI_ExcludeXS))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_ALLE3IS_SysOpsWrite_f68dcd86f3998afd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  (AArch64_TLBI_ALL w__1 Regime_EL3 Shareability_ISH TLBI_AllAttr))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_ALLE3OS_SysOpsWrite_7d60d9e9832a86fc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  (AArch64_TLBI_ALL w__1 Regime_EL3 Shareability_OSH TLBI_AllAttr))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_ALLE3OS_SysOpsWrite_f5180bd2c6904111 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__2 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                      (AArch64_TLBI_ALL w__2 Regime_EL3 Shareability_OSH TLBI_ExcludeXS))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_ALLE3_SysOpsWrite_154b769b60a9a83a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__2 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                      (AArch64_TLBI_ALL w__2 Regime_EL3 Shareability_NSH TLBI_ExcludeXS))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_ALLE3_SysOpsWrite_f67a5db4b11c6ca5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  (AArch64_TLBI_ALL w__1 Regime_EL3 Shareability_NSH TLBI_AllAttr))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_RVAE3IS_SysOpsWrite_61186878beebdd00 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__2 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                      let w__3 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_RVA w__2 Regime_EL3 w__3 Shareability_ISH TLBILevel_Any
                        TLBI_ExcludeXS w__4))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_RVAE3IS_SysOpsWrite_e7bda4e5b52e0dd2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  let w__2 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RVA w__1 Regime_EL3 w__2 Shareability_ISH TLBILevel_Any TLBI_AllAttr
                    w__3))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_RVAE3OS_SysOpsWrite_51cc3eac56f81d7f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  let w__2 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RVA w__1 Regime_EL3 w__2 Shareability_OSH TLBILevel_Any TLBI_AllAttr
                    w__3))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_RVAE3OS_SysOpsWrite_b68e938dbaed6553 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__2 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                      let w__3 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_RVA w__2 Regime_EL3 w__3 Shareability_OSH TLBILevel_Any
                        TLBI_ExcludeXS w__4))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_RVAE3_SysOpsWrite_9115183869722fc4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  let w__2 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RVA w__1 Regime_EL3 w__2 Shareability_NSH TLBILevel_Any TLBI_AllAttr
                    w__3))
              else (pure (())))))


end ArmFull.Functions
