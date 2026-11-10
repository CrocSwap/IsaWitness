import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0036
import ArmFull.Fn.M0044
import ArmFull.Fn.M0046
import ArmFull.Fn.M0047
import ArmFull.Fn.M0048
import ArmFull.Fn.M0113
import ArmFull.Fn.M0115
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0152
import ArmFull.Fn.M0154
import ArmFull.Fn.M0178
import ArmFull.Fn.M0180
import ArmFull.Fn.M0181

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

def InterruptPending (_ : Unit) : SailM Bool := do
  let fiq_pending ← (( do (undefined_bool_at (← occLabel 735) ()) ) : SailM Bool )
  let irq_pending ← (( do (undefined_bool_at (← occLabel 736) ()) ) : SailM Bool )
  let pending_virtual_interrupt : Bool := false
  let (__tup_0, _) ← (( do (IRQPending ()) ) : SailM (Bool × Bool) )
  let irq_pending : Bool := __tup_0
  let (__tup_0, _) := (FIQPending ())
  let fiq_pending : Bool := __tup_0
  let pending_physical_interrupt : Bool :=
    ((irq_pending || fiq_pending) || (IsPhysicalSErrorPending ()))
  let w__6 ← (( do
    if ((← do
         if ((← do
              (EL2Enabled ())) : Bool)
         then
           (do
             if ((← do
                  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__1.EL == EL0) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                 (pure (((w__2.EL == EL1) : Bool)))))
         else (pure false)) : Bool)
    then
      (do
        let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_TGE w__5) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let pending_virtual_interrupt ← (( do
    if (w__6 : Bool)
    then
      (do
        let virq_pending ← (( do
          if ((← do
               let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
               (pure ((((_get_HCR_EL2_Type_IMO w__7) == 1#1) : Bool)))) : Bool)
          then
            (do
              if ((← do
                   (VirtualIRQPending ())) : Bool)
              then (pure true)
              else
                (do
                  let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_VI w__9) == 1#1) : Bool)))))
          else (pure false) ) : SailM Bool )
        let vfiq_pending ← (( do
          if ((← do
               let w__11 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
               (pure ((((_get_HCR_EL2_Type_FMO w__11) == 1#1) : Bool)))) : Bool)
          then
            (do
              if ((← do
                   (VirtualFIQPending ())) : Bool)
              then (pure true)
              else
                (do
                  let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_VF w__13) == 1#1) : Bool)))))
          else (pure false) ) : SailM Bool )
        let vsei_pending ← (( do
          if ((← do
               let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
               (pure ((((_get_HCR_EL2_Type_AMO w__15) == 1#1) : Bool)))) : Bool)
          then
            (do
              if ((← do
                   (IsVirtualSErrorPending ())) : Bool)
              then (pure true)
              else
                (do
                  let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_VSE w__17) == 1#1) : Bool)))))
          else (pure false) ) : SailM Bool )
        let pending_virtual_interrupt : Bool := ((vsei_pending || virq_pending) || vfiq_pending)
        (pure (pending_virtual_interrupt)))
    else (pure (pending_virtual_interrupt)) ) : SailM Bool )
  (pure ((pending_physical_interrupt || pending_virtual_interrupt)))


def IsHCRXEL2Enabled (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (HaveFeatHCX ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let w__2 ← (( do
        if (((HaveEL EL3) : Bool) : Bool)
        then
          (do
            let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            (pure ((((_get_SCR_EL3_Type_HXEn w__1) == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__2 : Bool)
      then (pure (false))
      else
        (do
          (EL2Enabled ())))


def UsePrimarySpaceEL10 (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  if (((_get_MPAM3_EL3_Type_ALTSP_HEN w__0) == 0#1) : Bool)
  then
    (do
      let w__1 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
      (pure (((_get_MPAM3_EL3_Type_ALTSP_HFC w__1) == 0#1))))
  else
    (do
      if ((← do
           if ((← do
                let w__2 ← (( do (MPAMisEnabled ()) ) : SailM Bool )
                (pure (((! w__2) : Bool)))) : Bool)
           then (pure true)
           else
             (do
               let w__3 ← (( do (EL2Enabled ()) ) : SailM Bool )
               (pure (((! w__3) : Bool))))) : Bool)
      then (pure true)
      else
        (do
          let w__5 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
          (pure ((((_get_MPAM2_EL2_Type_ALTSP_HFC w__5) == 0#1) : Bool)))))


def MPAMisVirtual (el : (BitVec 2)) : SailM Bool := do
  if ((← do
       if ((← do
            let w__0 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
            (pure ((((_get_MPAMIDR_EL1_Type_HAS_HCR w__0) == 1#1) : Bool)))) : Bool)
       then
         (do
           (EL2Enabled ()))
       else (pure false)) : Bool)
  then
    (do
      if ((← do
           if ((← do
                if (((el == EL0) : Bool) : Bool)
                then
                  (do
                    let w__3 ← (( do readReg MPAMHCR_EL2 ) : SailM (BitVec 64) )
                    (pure ((((_get_MPAMHCR_EL2_Type_EL0_VPMEN w__3) == 1#1) : Bool))))
                else (pure false)) : Bool)
           then
             (do
               if ((← do
                    let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure ((((_get_HCR_EL2_Type_E2H w__5) == 0#1) : Bool)))) : Bool)
               then (pure true)
               else
                 (do
                   let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCR_EL2_Type_TGE w__6) == 0#1) : Bool)))))
           else (pure false)) : Bool)
      then (pure true)
      else
        (do
          if (((el == EL1) : Bool) : Bool)
          then
            (do
              let w__9 ← (( do readReg MPAMHCR_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_MPAMHCR_EL2_Type_EL1_VPMEN w__9) == 1#1) : Bool))))
          else (pure false)))
  else (pure false)


/-- Type quantifiers: k_InD : Bool, k_InSM : Bool -/
def getMPAM_PARTID (MPAMn : (BitVec 2)) (InD : Bool) (InSM : Bool) : SailM (BitVec 16) := do
  let partid ← (( do (undefined_bitvector_at (← occLabel 763) 16) ) : SailM PARTIDtype )
  let el2avail ← (( do (EL2Enabled ()) ) : SailM Bool )
  if (InSM : Bool)
  then
    (do
      let w__0 ← (( do readReg MPAMSM_EL1 ) : SailM (BitVec 64) )
      let partid := ((_get_MPAMSM_EL1_Type_PARTID_D w__0) : (BitVec 16))
      (pure (partid)))
  else
    (do
      if (InD : Bool)
      then
        (do
          match MPAMn with
          | 0b11 =>
            (do
              let w__1 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
              let partid := ((_get_MPAM3_EL3_Type_PARTID_I w__1) : (BitVec 16))
              (pure (partid)))
          | 0b10 =>
            (do
              if (el2avail : Bool)
              then
                (do
                  let w__2 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_MPAM2_EL2_Type_PARTID_I w__2))))
              else (pure ((Zeros (n := 16)))))
          | 0b01 =>
            (do
              let w__4 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
              let partid := ((_get_MPAM1_EL1_Type_PARTID_I w__4) : (BitVec 16))
              (pure (partid)))
          | 0b00 =>
            (do
              let w__5 ← (( do readReg MPAM0_EL1 ) : SailM (BitVec 64) )
              let partid := ((_get_MPAM0_EL1_Type_PARTID_I w__5) : (BitVec 16))
              (pure (partid)))
          | _ =>
            (do
              (__UNKNOWN_PARTIDtype ())))
      else
        (do
          match MPAMn with
          | 0b11 =>
            (do
              let w__7 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
              let partid := ((_get_MPAM3_EL3_Type_PARTID_D w__7) : (BitVec 16))
              (pure (partid)))
          | 0b10 =>
            (do
              if (el2avail : Bool)
              then
                (do
                  let w__8 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_MPAM2_EL2_Type_PARTID_D w__8))))
              else (pure ((Zeros (n := 16)))))
          | 0b01 =>
            (do
              let w__10 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
              let partid := ((_get_MPAM1_EL1_Type_PARTID_D w__10) : (BitVec 16))
              (pure (partid)))
          | 0b00 =>
            (do
              let w__11 ← (( do readReg MPAM0_EL1 ) : SailM (BitVec 64) )
              let partid := ((_get_MPAM0_EL1_Type_PARTID_D w__11) : (BitVec 16))
              (pure (partid)))
          | _ =>
            (do
              (__UNKNOWN_PARTIDtype ()))))


/-- Type quantifiers: k_InD : Bool, k_InSM : Bool -/
def getMPAM_PMG (MPAMn : (BitVec 2)) (InD : Bool) (InSM : Bool) : SailM (BitVec 8) := do
  let pmg ← (( do (undefined_bitvector_at (← occLabel 764) 8) ) : SailM PMGtype )
  let el2avail ← (( do (EL2Enabled ()) ) : SailM Bool )
  if (InSM : Bool)
  then
    (do
      let w__0 ← (( do readReg MPAMSM_EL1 ) : SailM (BitVec 64) )
      let pmg := ((_get_MPAMSM_EL1_Type_PMG_D w__0) : (BitVec 8))
      (pure (pmg)))
  else
    (do
      if (InD : Bool)
      then
        (do
          match MPAMn with
          | 0b11 =>
            (do
              let w__1 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
              let pmg := ((_get_MPAM3_EL3_Type_PMG_I w__1) : (BitVec 8))
              (pure (pmg)))
          | 0b10 =>
            (do
              if (el2avail : Bool)
              then
                (do
                  let w__2 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_MPAM2_EL2_Type_PMG_I w__2))))
              else (pure ((Zeros (n := 8)))))
          | 0b01 =>
            (do
              let w__4 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
              let pmg := ((_get_MPAM1_EL1_Type_PMG_I w__4) : (BitVec 8))
              (pure (pmg)))
          | 0b00 =>
            (do
              let w__5 ← (( do readReg MPAM0_EL1 ) : SailM (BitVec 64) )
              let pmg := ((_get_MPAM0_EL1_Type_PMG_I w__5) : (BitVec 8))
              (pure (pmg)))
          | _ =>
            (do
              (__UNKNOWN_PMGtype ())))
      else
        (do
          match MPAMn with
          | 0b11 =>
            (do
              let w__7 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
              let pmg := ((_get_MPAM3_EL3_Type_PMG_D w__7) : (BitVec 8))
              (pure (pmg)))
          | 0b10 =>
            (do
              if (el2avail : Bool)
              then
                (do
                  let w__8 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_MPAM2_EL2_Type_PMG_D w__8))))
              else (pure ((Zeros (n := 8)))))
          | 0b01 =>
            (do
              let w__10 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
              let pmg := ((_get_MPAM1_EL1_Type_PMG_D w__10) : (BitVec 8))
              (pure (pmg)))
          | 0b00 =>
            (do
              let w__11 ← (( do readReg MPAM0_EL1 ) : SailM (BitVec 64) )
              let pmg := ((_get_MPAM0_EL1_Type_PMG_D w__11) : (BitVec 8))
              (pure (pmg)))
          | _ =>
            (do
              (__UNKNOWN_PMGtype ()))))


def ExtAbortToA64 (fault : FaultRecord) : SailM Bool := do
  let route_to_aarch64 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  let w__5 ← (( do
    if ((← do
         if (((! route_to_aarch64) : Bool) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__4 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
        (pure (((! w__4) : Bool))))
    else (pure false) ) : SailM Bool )
  let route_to_aarch64 ← (( do
    if (w__5 : Bool)
    then
      (do
        if ((← do
             if ((← do
                  if ((← do
                       let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                       (pure ((((_get_HCR_EL2_Type_TGE w__6) == 1#1) : Bool)))) : Bool)
                  then (pure true)
                  else
                    (do
                      (IsSecondStage fault))) : Bool)
             then (pure true)
             else
               (do
                 if ((← do
                      if ((← do
                           (HaveRASExt ())) : Bool)
                      then
                        (do
                          let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure ((((_get_HCR_EL2_Type_TEA w__10) == 1#1) : Bool))))
                      else (pure false)) : Bool)
                 then
                   (do
                     (IsExternalAbort__1 fault))
                 else (pure false))) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 (IsDebugException fault)) : Bool)
            then
              (do
                let w__16 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_MDCR_EL2_Type_TDE w__16) == 1#1) : Bool))))
            else (pure false)))
    else (pure (route_to_aarch64)) ) : SailM Bool )
  let w__20 ← (( do
    if ((((! route_to_aarch64) && (HaveEL EL3)) : Bool) : Bool)
    then
      (do
        let w__19 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
        (pure (((! w__19) : Bool))))
    else (pure false) ) : SailM Bool )
  let route_to_aarch64 ← (( do
    if (w__20 : Bool)
    then
      (do
        if ((← do
             let w__21 ← (( do (SCR_GEN_read ()) ) : SailM (BitVec 64) )
             (pure ((((_get_SCRType_EA w__21) == 1#1) : Bool)))) : Bool)
        then
          (do
            (IsExternalAbort__1 fault))
        else (pure false))
    else (pure (route_to_aarch64)) ) : SailM Bool )
  if ((route_to_aarch64 : Bool) : Bool)
  then
    (do
      (IsExternalSyncAbort fault.statuscode))
  else (pure false)


def IsSCTLR2EL2Enabled (_ : Unit) : SailM Bool := do
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
          (EL2Enabled ())))


def AArch32_GeneralExceptionsToAArch64 (_ : Unit) : SailM Bool := do
  if ((← do
       if ((← do
            let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__0.EL == EL0) : Bool)))) : Bool)
       then
         (do
           let w__1 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
           (pure (((! w__1) : Bool))))
       else (pure false)) : Bool)
  then (pure true)
  else
    (do
      if ((← do
           if ((← do
                (EL2Enabled ())) : Bool)
           then
             (do
               let w__4 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
               (pure (((! w__4) : Bool))))
           else (pure false)) : Bool)
      then
        (do
          let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
          (pure ((((_get_HCR_EL2_Type_TGE w__6) == 1#1) : Bool))))
      else (pure false))


def TestEventCNTP (prev_physical_count : (BitVec 64)) (current_physical_count : (BitVec 64)) : SailM Unit := do
  let n ← (( do (undefined_int_at (.site 1179) ()) ) : SailM Int )
  let offset ← (( do (undefined_bitvector_at (.site 1180) 64) ) : SailM (BitVec 64) )
  let previousbit ← (( do (undefined_bitvector_at (.site 1181) 1) ) : SailM (BitVec 1) )
  let samplebit ← (( do (undefined_bitvector_at (.site 1182) 1) ) : SailM (BitVec 1) )
  let w__0 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let n ← (( do
    if (((_get_CNTHCTL_EL2_Type_EVNTEN w__0) == 1#1) : Bool)
    then
      (do
        let w__1 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
        let n : Int := ((BitVec.toNat (_get_CNTHCTL_EL2_Type_EVNTI w__1)) : Int)
        let w__4 ← (( do
          if ((← do
               (HaveECVExt ())) : Bool)
          then
            (do
              let w__3 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_CNTHCTL_EL2_Type_EVNTIS w__3) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let n : Int :=
          if (w__4 : Bool)
          then (n +i 8)
          else n
        let n : Int := n
        let ecv : Bool := false
        let w__5 ← (( do (HaveECVExt ()) ) : SailM Bool )
        let offset ← (( do
          if (w__5 : Bool)
          then
            (do
              let ecv ← (( do
                if ((← do
                     if ((← do
                          (EL2Enabled ())) : Bool)
                     then
                       (do
                         let w__7 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
                         (pure ((((_get_CNTHCTL_EL2_Type_ECV w__7) == 1#1) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__9 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    (pure ((((_get_SCR_EL3_Type_ECVEn w__9) == 1#1) : Bool))))
                else (pure false) ) : SailM Bool )
              if (ecv : Bool)
              then
                (do
                  readReg CNTPOFF_EL2)
              else (pure ((Zeros (n := 64)))))
          else (pure (offset)) ) : SailM (BitVec 64) )
        ArmFull.assert ((0 ≤b n) && (n <b 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:18360.46-18360.47"
        let samplebit : (BitVec 1) :=
          (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access (current_physical_count - offset)
              (Sail.Int.toNatChecked (n)))]))
        let previousbit : (BitVec 1) :=
          (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access (prev_physical_count - offset)
              (Sail.Int.toNatChecked (n)))]))
        let w__12 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
        if (((_get_CNTHCTL_EL2_Type_EVNTDIR w__12) == 0#1) : Bool)
        then
          (do
            if (((previousbit == 0#1) && (samplebit == 1#1)) : Bool)
            then
              (do
                (SetEventRegister ()))
            else (pure (())))
        else
          (do
            if (((previousbit == 1#1) && (samplebit == 0#1)) : Bool)
            then
              (do
                (SetEventRegister ()))
            else (pure (())))
        (pure (n)))
    else (pure (n)) ) : SailM Int )
  let n : Int := n
  (pure (()))


def TestEventCNTV (prev_physical_count : (BitVec 64)) (current_physical_count : (BitVec 64)) : SailM Unit := do
  let n ← (( do (undefined_int_at (.site 1184) ()) ) : SailM Int )
  let offset ← (( do (undefined_bitvector_at (.site 1185) 64) ) : SailM (BitVec 64) )
  let previousbit ← (( do (undefined_bitvector_at (.site 1186) 1) ) : SailM (BitVec 1) )
  let samplebit ← (( do (undefined_bitvector_at (.site 1187) 1) ) : SailM (BitVec 1) )
  let w__5 ← (( do
    if ((← do
         let w__3 ← (( do
           if ((← do
                (HaveVirtHostExt ())) : Bool)
           then
             (do
               let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
               let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
               (pure (((((_get_HCR_EL2_Type_E2H w__1) +++ (_get_HCR_EL2_Type_TGE w__2)) == 0b11#2) : Bool))))
           else (pure false) ) : SailM Bool )
         (pure (((! w__3) : Bool)))) : Bool)
    then
      (do
        let w__4 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
        (pure ((((_get_CNTKCTL_EL1_Type_EVNTEN w__4) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let n ← (( do
    if (w__5 : Bool)
    then
      (do
        let w__6 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
        let n : Int := ((BitVec.toNat (_get_CNTKCTL_EL1_Type_EVNTI w__6)) : Int)
        let w__9 ← (( do
          if ((← do
               (HaveECVExt ())) : Bool)
          then
            (do
              let w__8 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
              (pure ((((_get_CNTKCTL_EL1_Type_EVNTIS w__8) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let n : Int :=
          if (w__9 : Bool)
          then (n +i 8)
          else n
        let n : Int := n
        let w__14 ← (( do
          if (((HaveEL EL2) : Bool) : Bool)
          then
            (do
              if ((← do
                   let w__10 ← (( do (EL2Enabled ()) ) : SailM Bool )
                   (pure (((! w__10) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__11 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__12 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure (((((_get_HCR_EL2_Type_E2H w__11) +++ (_get_HCR_EL2_Type_TGE w__12)) != 0b11#2) : Bool)))))
          else (pure false) ) : SailM Bool )
        let offset ← (( do
          if (w__14 : Bool)
          then
            (do
              readReg CNTVOFF_EL2)
          else
            (let offset : (BitVec 64) := (Zeros (n := 64))
            (pure (offset))) ) : SailM (BitVec 64) )
        ArmFull.assert ((0 ≤b n) && (n <b 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:18411.46-18411.47"
        let samplebit : (BitVec 1) :=
          (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access (current_physical_count - offset)
              (Sail.Int.toNatChecked (n)))]))
        let previousbit : (BitVec 1) :=
          (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access (prev_physical_count - offset)
              (Sail.Int.toNatChecked (n)))]))
        let w__16 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
        if (((_get_CNTKCTL_EL1_Type_EVNTDIR w__16) == 0#1) : Bool)
        then
          (do
            if (((previousbit == 0#1) && (samplebit == 1#1)) : Bool)
            then
              (do
                (SetEventRegister ()))
            else (pure (())))
        else
          (do
            if (((previousbit == 1#1) && (samplebit == 0#1)) : Bool)
            then
              (do
                (SetEventRegister ()))
            else (pure (())))
        (pure (n)))
    else (pure (n)) ) : SailM Int )
  let n : Int := n
  (pure (()))


end ArmFull.Functions
