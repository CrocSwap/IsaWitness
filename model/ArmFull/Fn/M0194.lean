import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0025
import ArmFull.Fn.M0034
import ArmFull.Fn.M0035
import ArmFull.Fn.M0036
import ArmFull.Fn.M0100
import ArmFull.Fn.M0108
import ArmFull.Fn.M0144
import ArmFull.Fn.M0178
import ArmFull.Fn.M0179
import ArmFull.Fn.M0180
import ArmFull.Fn.M0181
import ArmFull.Fn.M0186

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

/-- Type quantifiers: idx : Nat, 0 ≤ idx ∧ idx ≤ 32 -/
def CountPMUEvents (idx : Nat) : SailM Bool := do
  let dp ← (( do (undefined_bitvector_at (← occLabel 530) 1) ) : SailM (BitVec 1) )
  let hccd ← (( do (undefined_bitvector_at (← occLabel 531) 1) ) : SailM (BitVec 1) )
  let hpmd ← (( do (undefined_bitvector_at (← occLabel 532) 1) ) : SailM (BitVec 1) )
  let sccd ← (( do (undefined_bitvector_at (← occLabel 533) 1) ) : SailM (BitVec 1) )
  let num_counters ← (( do (GetNumEventCounters ()) ) : SailM Int )
  let w__2 ← (( do
    if ((((idx == CYCLE_COUNTER_ID) || (idx <b num_counters)) : Bool) : Bool)
    then (pure true)
    else
      (do
        if (((idx == INSTRUCTION_COUNTER_ID) : Bool) : Bool)
        then
          (do
            (HavePMUv3ICNTR ()))
        else (pure false)) ) : SailM Bool )
  ArmFull.assert w__2 "sail-arm/v8_base.sail:4945.108-4945.109"
  let enabled ← (( do (undefined_bool_at (← occLabel 534) ()) ) : SailM Bool )
  let filtered ← (( do (undefined_bool_at (← occLabel 535) ()) ) : SailM Bool )
  let E ← (( do (undefined_bitvector_at (← occLabel 536) 1) ) : SailM (BitVec 1) )
  let debug ← (( do (Halted ()) ) : SailM Bool )
  let resvd_for_el2 ← (( do (PMUCounterIsHyp idx) ) : SailM Bool )
  let ss ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
  let questionMark : Nat := idx
  let enabled ← (( do
    if ((questionMark == INSTRUCTION_COUNTER_ID) : Bool)
    then
      (do
        let w__3 ← (( do (HaveAArch64 ()) ) : SailM Bool )
        ArmFull.assert w__3 "sail-arm/v8_base.sail:4954.30-4954.31"
        if ((← do
             let w__4 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
             (pure ((((_get_PMCR_EL0_Type_E w__4) == 1#1) : Bool)))) : Bool)
        then
          (do
            let w__5 ← (( do readReg PMCNTENSET_EL0 ) : SailM (BitVec 64) )
            (pure ((((_get_PMCNTENSET_EL0_Type_F0 w__5) == 1#1) : Bool))))
        else (pure false))
    else
      (do
        if ((questionMark == CYCLE_COUNTER_ID) : Bool)
        then
          (do
            let w__7 ← (( do (HaveAArch64 ()) ) : SailM Bool )
            if (w__7 : Bool)
            then
              (do
                if ((← do
                     let w__8 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
                     (pure ((((_get_PMCR_EL0_Type_E w__8) == 1#1) : Bool)))) : Bool)
                then
                  (do
                    let w__9 ← (( do readReg PMCNTENSET_EL0 ) : SailM (BitVec 64) )
                    (pure ((((_get_PMCNTENSET_EL0_Type_C w__9) == 1#1) : Bool))))
                else (pure false))
            else
              (do
                if ((← do
                     let w__11 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
                     (pure ((((_get_PMCR_Type_E w__11) == 1#1) : Bool)))) : Bool)
                then
                  (do
                    let w__12 ← (( do (PMCNTENSET_read ()) ) : SailM (BitVec 32) )
                    (pure ((((_get_PMCNTENSET_Type_C w__12) == 1#1) : Bool))))
                else (pure false)))
        else
          (do
            let E ← (( do
              if (resvd_for_el2 : Bool)
              then
                (do
                  let w__14 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                  if (w__14 : Bool)
                  then
                    (do
                      let w__15 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                      (pure ((_get_MDCR_EL2_Type_HPME w__15))))
                  else
                    (do
                      let w__16 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                      (pure ((_get_HDCR_Type_HPME w__16)))))
              else
                (do
                  let w__18 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                  if (w__18 : Bool)
                  then
                    (do
                      let w__19 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
                      (pure ((_get_PMCR_EL0_Type_E w__19))))
                  else
                    (do
                      let w__20 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
                      (pure ((_get_PMCR_Type_E w__20))))) ) : SailM (BitVec 1) )
            let w__22 ← (( do (HaveAArch64 ()) ) : SailM Bool )
            if (w__22 : Bool)
            then
              (do
                if (((E == 1#1) : Bool) : Bool)
                then
                  (do
                    let w__23 ← (( do readReg PMCNTENSET_EL0 ) : SailM (BitVec 64) )
                    (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__23 idx)])) == 1#1) : Bool))))
                else (pure false))
            else
              (do
                ArmFull.assert ((0 ≤b idx) && (idx <b 32)) "sail-arm/v8_base.sail:4973.56-4973.57"
                if (((E == 1#1) : Bool) : Bool)
                then
                  (do
                    let w__25 ← (( do (PMCNTENSET_read ()) ) : SailM (BitVec 32) )
                    (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__25 idx)])) == 1#1) : Bool))))
                else (pure false)))) ) : SailM Bool )
  let prohibited : Bool := false
  let prohibited ← (( do
    if (((HaveEL EL3) && (BEq.beq ss SS_Secure)) : Bool)
    then
      (do
        let w__27 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
        let prohibited ← (( do
          if ((! w__27) : Bool)
          then
            (do
              if ((← do
                   if ((← do
                        let w__28 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                        (pure ((((_get_MDCR_EL3_Type_SPME w__28) == 0#1) : Bool)))) : Bool)
                   then
                     (do
                       (HavePMUv3p7 ()))
                   else (pure false)) : Bool)
              then
                (do
                  let w__31 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                  (pure ((((_get_MDCR_EL3_Type_MPMX w__31) == 0#1) : Bool))))
              else (pure false))
          else
            (do
              let w__33 ← (( do readReg SDCR ) : SailM (BitVec 32) )
              let prohibited := (((_get_SDCR_Type_SPME w__33) == 0#1) : Bool)
              (pure (prohibited))) ) : SailM Bool )
        let w__35 ← (( do
          if ((prohibited : Bool) : Bool)
          then
            (do
              let w__34 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__34.EL == EL0) : Bool))))
          else (pure false) ) : SailM Bool )
        if (w__35 : Bool)
        then
          (do
            let w__36 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
            if (w__36 : Bool)
            then
              (do
                let w__37 ← (( do (SDER_read ()) ) : SailM (BitVec 32) )
                let prohibited := (((_get_SDER_Type_SUNIDEN w__37) == 0#1) : Bool)
                (pure (prohibited)))
            else
              (do
                let w__38 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                if (w__38 : Bool)
                then
                  (do
                    let w__39 ← (( do (SDER32_EL3_read ()) ) : SailM (BitVec 64) )
                    let prohibited := (((_get_SDER32_EL3_Type_SUNIDEN w__39) == 0#1) : Bool)
                    (pure (prohibited)))
                else (pure (prohibited))))
        else (pure (prohibited)))
    else (pure (prohibited)) ) : SailM Bool )
  let w__45 ← (( do
    if ((← do
         if ((← do
              if (((! prohibited) : Bool) : Bool)
              then
                (do
                  (HavePMUv3p7 ()))
              else (pure false)) : Bool)
         then
           (do
             let w__42 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__42.EL == EL3) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        (HaveAArch64 ()))
    else (pure false) ) : SailM Bool )
  let prohibited ← (( do
    if (w__45 : Bool)
    then
      (do
        if ((← do
             let w__46 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
             (pure ((((_get_MDCR_EL3_Type_MPMX w__46) == 1#1) : Bool)))) : Bool)
        then
          (pure ((← do
                let w__47 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                (pure ((((_get_MDCR_EL3_Type_SPME w__47) == 0#1) : Bool)))) || (! resvd_for_el2)))
        else (pure false))
    else (pure (prohibited)) ) : SailM Bool )
  let w__54 ← (( do
    (pure ((← do
          if ((← do
               if (((! prohibited) : Bool) : Bool)
               then
                 (do
                   let w__50 ← (( do readReg PSTATE ) : SailM ProcState )
                   (pure (((w__50.EL == EL2) : Bool))))
               else (pure false)) : Bool)
          then
            (do
              (HaveHPMDExt ()))
          else (pure false)) && (! resvd_for_el2))) ) : SailM Bool )
  let prohibited ← (( do
    if (w__54 : Bool)
    then
      (do
        let w__55 ← (( do (HaveAArch64 ()) ) : SailM Bool )
        let hpmd ← (( do
          if (w__55 : Bool)
          then
            (do
              let w__56 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_MDCR_EL2_Type_HPMD w__56))))
          else
            (do
              let w__57 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
              (pure ((_get_HDCR_Type_HPMD w__57)))) ) : SailM (BitVec 1) )
        let prohibited : Bool := (hpmd == 1#1)
        (pure (prohibited)))
    else (pure (prohibited)) ) : SailM Bool )
  let w__59 ← (( do
    if ((prohibited : Bool) : Bool)
    then
      (do
        let w__58 ← (( do (HaveNoSecurePMUDisableOverride ()) ) : SailM Bool )
        (pure (((! w__58) : Bool))))
    else (pure false) ) : SailM Bool )
  let prohibited ← (( do
    if (w__59 : Bool)
    then
      (do
        let w__60 ← (( do (ExternalSecureNoninvasiveDebugEnabled ()) ) : SailM Bool )
        let prohibited := ((! w__60) : Bool)
        (pure (prohibited)))
    else (pure (prohibited)) ) : SailM Bool )
  let frozen : Bool := false
  let w__61 ← (( do (HavePMUv3p7 ()) ) : SailM Bool )
  let frozen ← (( do
    if (w__61 : Bool)
    then
      (do
        let FZ ← (( do (undefined_bitvector_at (← occLabel 537) 1) ) : SailM (BitVec 1) )
        let FZ ← (( do
          if (resvd_for_el2 : Bool)
          then
            (do
              let w__62 ← (( do (HaveAArch64 ()) ) : SailM Bool )
              if (w__62 : Bool)
              then
                (do
                  let w__63 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_MDCR_EL2_Type_HPMFZO w__63))))
              else
                (do
                  let w__64 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                  (pure ((_get_HDCR_Type_HPMFZO w__64)))))
          else
            (do
              let w__66 ← (( do (HaveAArch64 ()) ) : SailM Bool )
              if (w__66 : Bool)
              then
                (do
                  let w__67 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
                  (pure ((_get_PMCR_EL0_Type_FZO w__67))))
              else
                (do
                  let w__68 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
                  (pure ((_get_PMCR_Type_FZO w__68))))) ) : SailM (BitVec 1) )
        if (((FZ == 1#1) : Bool) : Bool)
        then
          (do
            (HiLoPMUOverflow resvd_for_el2))
        else (pure false))
    else (pure (frozen)) ) : SailM Bool )
  let (enabled, frozen, prohibited) ← (( do
    if (((prohibited || frozen) && (idx == CYCLE_COUNTER_ID)) : Bool)
    then
      (do
        let w__72 ← (( do (HaveAArch64 ()) ) : SailM Bool )
        let dp ← (( do
          if (w__72 : Bool)
          then
            (do
              let w__73 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
              (pure ((_get_PMCR_EL0_Type_DP w__73))))
          else
            (do
              let w__74 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
              (pure ((_get_PMCR_Type_DP w__74)))) ) : SailM (BitVec 1) )
        let enabled : Bool := (enabled && (dp == 0#1))
        let prohibited : Bool := false
        let frozen : Bool := false
        (pure ((enabled, frozen, prohibited))))
    else (pure ((enabled, frozen, prohibited))) ) : SailM (Bool × Bool × Bool) )
  let w__76 ← (( do
    (pure ((← do
          (HavePMUv3p5 ())) && ((idx == CYCLE_COUNTER_ID) : Bool))) ) : SailM Bool )
  let prohibited ← (( do
    if (w__76 : Bool)
    then
      (do
        let prohibited ← (( do
          if (((HaveEL EL3) && (BEq.beq ss SS_Secure)) : Bool)
          then
            (do
              let w__77 ← (( do (HaveAArch64 ()) ) : SailM Bool )
              let sccd ← (( do
                if (w__77 : Bool)
                then
                  (do
                    let w__78 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                    (pure ((_get_MDCR_EL3_Type_SCCD w__78))))
                else
                  (do
                    let w__79 ← (( do readReg SDCR ) : SailM (BitVec 32) )
                    (pure ((_get_SDCR_Type_SCCD w__79)))) ) : SailM (BitVec 1) )
              let prohibited : Bool :=
                if ((sccd == 1#1) : Bool)
                then true
                else prohibited
              (pure (prohibited)))
          else (pure (prohibited)) ) : SailM Bool )
        let w__80 ← (( do readReg PSTATE ) : SailM ProcState )
        if ((w__80.EL == EL2) : Bool)
        then
          (do
            let w__81 ← (( do (HaveAArch64 ()) ) : SailM Bool )
            let hccd ← (( do
              if (w__81 : Bool)
              then
                (do
                  let w__82 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_MDCR_EL2_Type_HCCD w__82))))
              else
                (do
                  let w__83 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                  (pure ((_get_HDCR_Type_HCCD w__83)))) ) : SailM (BitVec 1) )
            let prohibited : Bool :=
              if ((hccd == 1#1) : Bool)
              then true
              else prohibited
            (pure (prohibited)))
        else (pure (prohibited)))
    else (pure (prohibited)) ) : SailM Bool )
  let w__85 ← (( do
    (pure ((← do
          (HavePMUv3p7 ())) && ((idx == CYCLE_COUNTER_ID) : Bool))) ) : SailM Bool )
  let prohibited ← (( do
    if (w__85 : Bool)
    then
      (do
        let w__90 ← (( do
          if ((← do
               if ((← do
                    let w__86 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__86.EL == EL3) : Bool)))) : Bool)
               then
                 (do
                   (HaveAArch64 ()))
               else (pure false)) : Bool)
          then
            (do
              let w__89 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
              (pure ((((_get_MDCR_EL3_Type_MCCD w__89) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let prohibited : Bool :=
          if (w__90 : Bool)
          then true
          else prohibited
        (pure (prohibited)))
    else (pure (prohibited)) ) : SailM Bool )
  let filter ← (( do (undefined_bitvector_at (← occLabel 538) 32) ) : SailM (BitVec 32) )
  let questionMark : Nat := idx
  let filter ← (( do
    if ((questionMark == INSTRUCTION_COUNTER_ID) : Bool)
    then
      (do
        let w__91 ← (( do readReg PMICFILTR_EL0 ) : SailM (BitVec 64) )
        let filter := ((Sail.BitVec.extractLsb w__91 31 0) : (BitVec 32))
        (pure (filter)))
    else
      (do
        if ((questionMark == CYCLE_COUNTER_ID) : Bool)
        then
          (do
            let w__92 ← (( do (HaveAArch64 ()) ) : SailM Bool )
            if (w__92 : Bool)
            then
              (do
                let w__93 ← (( do readReg PMCCFILTR_EL0 ) : SailM (BitVec 64) )
                (pure ((Sail.BitVec.extractLsb w__93 31 0))))
            else
              (do
                (PMCCFILTR_read ())))
        else
          (do
            let w__96 ← (( do (HaveAArch64 ()) ) : SailM Bool )
            if (w__96 : Bool)
            then
              (do
                ArmFull.assert ((0 ≤b idx) && (idx <b 32)) "sail-arm/v8_base.sail:5058.56-5058.57"
                let w__97 ← (( do readReg PMEVTYPER_EL0 ) : SailM (Vector (BitVec 64) 32) )
                (pure ((Sail.BitVec.extractLsb (GetElem?.getElem! w__97 idx) 31 0))))
            else
              (do
                ArmFull.assert ((0 ≤b idx) && (idx <b 31)) "sail-arm/v8_base.sail:5061.56-5061.57"
                (PMEVTYPER_read idx)))) ) : SailM (BitVec 32) )
  let filter := filter
  let P : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 31)]))
  let U : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 30)]))
  let NSK : (BitVec 1) :=
    if ((HaveEL EL3) : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 29)]))
    else 0#1
  let NSU : (BitVec 1) :=
    if ((HaveEL EL3) : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 28)]))
    else 0#1
  let NSH : (BitVec 1) :=
    if ((HaveEL EL2) : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 27)]))
    else 0#1
  let w__101 ← (( do
    if (((HaveEL EL3) : Bool) : Bool)
    then
      (do
        (HaveAArch64 ()))
    else (pure false) ) : SailM Bool )
  let M : (BitVec 1) :=
    if (w__101 : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 26)]))
    else 0#1
  let w__103 ← (( do
    if (((HaveEL EL3) : Bool) : Bool)
    then
      (do
        (HaveSecureEL2Ext ()))
    else (pure false) ) : SailM Bool )
  let SH : (BitVec 1) :=
    if (w__103 : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 24)]))
    else 0#1
  let w__104 ← (( do (HaveRME ()) ) : SailM Bool )
  let RLK : (BitVec 1) :=
    if (w__104 : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 22)]))
    else 0#1
  let w__105 ← (( do (HaveRME ()) ) : SailM Bool )
  let RLU : (BitVec 1) :=
    if (w__105 : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 21)]))
    else 0#1
  let w__106 ← (( do (HaveRME ()) ) : SailM Bool )
  let RLH : (BitVec 1) :=
    if (w__106 : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 20)]))
    else 0#1
  let ss ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
  let w__107 ← (( do readReg PSTATE ) : SailM ProcState )
  let questionMark := w__107.EL
  let filtered ← (( do
    if ((questionMark == EL0) : Bool)
    then
      (let filtered : Bool :=
        match ss with
        | .SS_NonSecure => (U != NSU)
        | .SS_Secure => (U == 1#1)
        | .SS_Realm => (U != RLU)
        | _ => filtered
      (pure (filtered)))
    else
      (do
        if ((questionMark == EL1) : Bool)
        then
          (let filtered : Bool :=
            match ss with
            | .SS_NonSecure => (P != NSK)
            | .SS_Secure => (P == 1#1)
            | .SS_Realm => (P != RLK)
            | _ => filtered
          (pure (filtered)))
        else
          (do
            if ((questionMark == EL2) : Bool)
            then
              (let filtered : Bool :=
                match ss with
                | .SS_NonSecure => (NSH == 0#1)
                | .SS_Secure => (NSH == SH)
                | .SS_Realm => (NSH == RLH)
                | _ => filtered
              (pure (filtered)))
            else
              (do
                if ((questionMark == EL3) : Bool)
                then
                  (do
                    let w__108 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                    let filtered : Bool :=
                      if (w__108 : Bool)
                      then (M != P)
                      else (P == 1#1)
                    (pure (filtered)))
                else (pure (filtered))))) ) : SailM Bool )
  (pure ((((((! debug) && enabled) && (! prohibited)) && (! filtered)) && (! frozen))))


def BranchRecordAllowed (el : (BitVec 2)) : SailM Bool := do
  let w__0 ← (( do (ELUsingAArch32 el) ) : SailM Bool )
  if (w__0 : Bool)
  then (pure (false))
  else
    (do
      let w__1 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      if (((_get_BRBFCR_EL1_Type_PAUSED w__1) == 1#1) : Bool)
      then (pure (false))
      else
        (do
          let w__3 ← (( do
            if (((el == EL3) : Bool) : Bool)
            then
              (do
                (HaveBRBEv1p1 ()))
            else (pure false) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              let w__4 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
              let w__5 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
              (pure (((_get_MDCR_EL3_Type_E3BREC w__4) != (_get_MDCR_EL3_Type_E3BREW w__5)))))
          else
            (do
              let w__11 ← (( do
                if (((HaveEL EL3) : Bool) : Bool)
                then
                  (do
                    if ((← do
                         let w__6 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                         (pure ((((_get_MDCR_EL3_Type_SBRBE w__6) == 0b00#2) : Bool)))) : Bool)
                    then (pure true)
                    else
                      (do
                        if ((← do
                             let w__7 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
                             (pure (((BEq.beq w__7 SS_Secure) : Bool)))) : Bool)
                        then
                          (do
                            let w__8 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                            (pure ((((_get_MDCR_EL3_Type_SBRBE w__8) == 0b01#2) : Bool))))
                        else (pure false)))
                else (pure false) ) : SailM Bool )
              if (w__11 : Bool)
              then (pure (false))
              else
                (do
                  let questionMark := el
                  if ((questionMark == EL3) : Bool)
                  then (pure (false))
                  else
                    (do
                      if ((questionMark == EL2) : Bool)
                      then
                        (do
                          let w__12 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((_get_BRBCR_EL2_Type_E2BRE w__12) == 1#1))))
                      else
                        (do
                          if ((questionMark == EL1) : Bool)
                          then
                            (do
                              let w__13 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
                              (pure (((_get_BRBCR_EL1_Type_E1BRE w__13) == 1#1))))
                          else
                            (do
                              if ((questionMark == EL0) : Bool)
                              then
                                (do
                                  let w__16 ← (( do
                                    if ((← do
                                         (EL2Enabled ())) : Bool)
                                    then
                                      (do
                                        let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        (pure ((((_get_HCR_EL2_Type_TGE w__15) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__16 : Bool)
                                  then
                                    (do
                                      let w__17 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
                                      (pure (((_get_BRBCR_EL2_Type_E0HBRE w__17) == 1#1))))
                                  else
                                    (do
                                      let w__18 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
                                      (pure (((_get_BRBCR_EL1_Type_E0BRE w__18) == 1#1)))))
                              else
                                (do
                                  (undefined_bool_at (← occLabel 562) ())))))))))


end ArmFull.Functions
