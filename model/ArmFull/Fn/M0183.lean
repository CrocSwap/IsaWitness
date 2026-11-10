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
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0035
import ArmFull.Fn.M0040
import ArmFull.Fn.M0042
import ArmFull.Fn.M0087
import ArmFull.Fn.M0097
import ArmFull.Fn.M0100
import ArmFull.Fn.M0108
import ArmFull.Fn.M0144
import ArmFull.Fn.M0153
import ArmFull.Fn.M0154
import ArmFull.Fn.M0172
import ArmFull.Fn.M0178
import ArmFull.Fn.M0179
import ArmFull.Fn.M0180
import ArmFull.Fn.M0181
import ArmFull.Fn.M0182

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

def AArch64_GetNumEventCountersAccessible (_ : Unit) : SailM Int := do
  let n ← (( do (undefined_int_at (← occLabel 501) ()) ) : SailM Int )
  let total_counters ← (( do (GetNumEventCounters ()) ) : SailM Int )
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__0.EL == EL1) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL0) : Bool))))) : Bool)
    then
      (do
        (EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let n ← (( do
    if (w__4 : Bool)
    then
      (do
        let w__5 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
        let n : Int := ((BitVec.toNat (_get_MDCR_EL2_Type_HPMN w__5)) : Int)
        let w__8 ← (( do
          if (((n >b total_counters) : Bool) : Bool)
          then (pure true)
          else
            (do
              (pure ((← do
                    let w__6 ← (( do (HaveFeatHPMN0 ()) ) : SailM Bool )
                    (pure (((! w__6) : Bool)))) && ((n == 0) : Bool)))) ) : SailM Bool )
        if (w__8 : Bool)
        then
          (do
            let (_, __tup_1) ← (( do
              (ConstrainUnpredictableInteger 0 total_counters Unpredictable_PMUEVENTCOUNTER) ) :
              SailM (Constraint × Int) )
            (pure (__tup_1)))
        else (pure (n)))
    else (pure (total_counters)) ) : SailM Int )
  let n : Int := n
  (pure (n))


def SecurityStateAtEL (EL : (BitVec 2)) : SailM SecurityState := SailME.run do
  let effective_nse_ns ← (( do (undefined_bitvector_at (← occLabel 503) 2) ) : SailME
    SecurityState (BitVec 2) )
  let w__0 ← (( do (HaveRME ()) ) : SailME SecurityState Bool )
  if (w__0 : Bool)
  then
    (do
      if ((EL == EL3) : Bool)
      then
        (do
          SailME.throw (SS_Root : SecurityState))
      else
        (do
          let w__1 ← (( do readReg SCR_EL3 ) : SailME SecurityState (BitVec 64) )
          let w__2 ← (( do (EffectiveSCR_EL3_NS ()) ) : SailME SecurityState (BitVec 1) )
          let effective_nse_ns : (BitVec 2) := ((_get_SCR_EL3_Type_NSE w__1) +++ w__2)
          match effective_nse_ns with
          | 0b00 =>
            (do
              let w__3 ← (( do (HaveSecureEL2Ext ()) ) : SailME SecurityState Bool )
              if (w__3 : Bool)
              then
                (do
                  SailME.throw (SS_Secure : SecurityState))
              else
                (do
                  (Unreachable ())))
          | 0b01 =>
            (do
              SailME.throw (SS_NonSecure : SecurityState))
          | 0b11 =>
            (do
              SailME.throw (SS_Realm : SecurityState))
          | _ =>
            (do
              (Unreachable ()))))
  else (pure (()))
  if ((! (HaveEL EL3)) : Bool)
  then
    (do
      let w__4 ← (( do (SecureOnlyImplementation ()) ) : SailME SecurityState Bool )
      let w__5 : SecurityState :=
        if (w__4 : Bool)
        then SS_Secure
        else SS_NonSecure
      (pure (w__5)))
  else
    (do
      if ((EL == EL3) : Bool)
      then (pure (SS_Secure))
      else
        (do
          let w__7 ← (( do
            if (((EL != EL2) : Bool) : Bool)
            then (pure true)
            else
              (do
                (EL2Enabled ())) ) : SailME SecurityState Bool )
          ArmFull.assert w__7 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:4136.39-4136.40"
          let w__8 ← (( do (ELUsingAArch32 EL3) ) : SailME SecurityState Bool )
          if ((! w__8) : Bool)
          then
            (do
              let w__9 ← (( do readReg SCR_EL3 ) : SailME SecurityState (BitVec 64) )
              let w__10 : SecurityState :=
                if (((_get_SCR_EL3_Type_NS w__9) == 1#1) : Bool)
                then SS_NonSecure
                else SS_Secure
              (pure (w__10)))
          else
            (do
              let w__11 ← (( do readReg SCR ) : SailME SecurityState (BitVec 32) )
              let w__12 : SecurityState :=
                if (((_get_SCR_Type_NS w__11) == 1#1) : Bool)
                then SS_NonSecure
                else SS_Secure
              (pure (w__12)))))


/-- Type quantifiers: k_check_cnten : Bool, k_check_e : Bool, k_check_inten : Bool, k_exclude_cyc :
  Bool, k_exclude_sync : Bool, k_include_hi_name : Bool, k_include_lo_name : Bool -/
def PMUOverflowCondition (check_e : Bool) (check_cnten : Bool) (check_inten : Bool) (include_hi_name : Bool) (include_lo_name : Bool) (exclude_cyc : Bool) (exclude_sync : Bool) : SailM Bool := do
  let counters ← (( do (GetNumEventCounters ()) ) : SailM Int )
  let ovsf ← (( do (undefined_bitvector_at (← occLabel 516) 64) ) : SailM (BitVec 64) )
  let w__0 ← (( do (HaveAArch64 ()) ) : SailM Bool )
  let ovsf ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do readReg PMOVSCLR_EL0 ) : SailM (BitVec 64) )
        let ovsf := (w__1 : (BitVec 64))
        let ovsf : (BitVec 64) := (Sail.BitVec.updateSubrange ovsf 63 33 (Zeros (n := 31)))
        let w__2 ← (( do (HavePMUv3ICNTR ()) ) : SailM Bool )
        let ovsf : (BitVec 64) :=
          if ((! w__2) : Bool)
          then (BitVec.update ovsf INSTRUCTION_COUNTER_ID (Bit 0#1))
          else ovsf
        (pure (ovsf)))
    else
      (do
        let w__3 ← (( do (PMOVSR_read ()) ) : SailM (BitVec 32) )
        let ovsf := ((Sail.BitVec.zeroExtend w__3 64) : (BitVec 64))
        (pure (ovsf))) ) : SailM (BitVec 64) )
  let ovsf ← (( do
    if ((counters <b 31) : Bool)
    then
      (do
        ArmFull.assert ((0 ≤b counters) && (counters ≤b 30)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:4603.61-4603.62"
        let ovsf : (BitVec 64) :=
          (Sail.BitVec.castWidth (Sail.BitVec.updateSubrange ovsf 30
            (Sail.Int.toNatChecked (counters))
            (Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked ((31 -i counters))))))))
        (pure (ovsf)))
    else (pure (ovsf)) ) : SailM (BitVec 64) )
  let ovsf ← (( do
    let loop_idx_lower : Nat := 0
    let loop_idx_upper : Int := (counters -i 1)
    (do
      let mut loop_vars := ovsf
      for idx in [loop_idx_lower:loop_idx_upper:1]i do
        let ovsf := loop_vars
        loop_vars ← do
          let E ← (( do (undefined_bitvector_at (← occLabel 517) 1) ) : SailM (BitVec 1) )
          let is_hyp ← (( do (PMUCounterIsHyp idx) ) : SailM Bool )
          let w__4 ← (( do (HaveAArch64 ()) ) : SailM Bool )
          let E ← (( do
            if (w__4 : Bool)
            then
              (do
                if (is_hyp : Bool)
                then
                  (do
                    let w__5 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                    (pure ((_get_MDCR_EL2_Type_HPME w__5))))
                else
                  (do
                    let w__6 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
                    (pure ((_get_PMCR_EL0_Type_E w__6)))))
            else
              (do
                if (is_hyp : Bool)
                then
                  (do
                    let w__8 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                    (pure ((_get_HDCR_Type_HPME w__8))))
                else
                  (do
                    let w__9 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
                    (pure ((_get_PMCR_Type_E w__9))))) ) : SailM (BitVec 1) )
          let ovsf ← (( do
            if (check_e : Bool)
            then
              (do
                ArmFull.assert ((0 ≤b idx) && (idx <b 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:4615.64-4615.65"
                let ovsf : (BitVec 64) :=
                  (BitVec.update ovsf (Sail.Int.toNatChecked (idx))
                    (Bit
                      ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ovsf
                            (Sail.Int.toNatChecked (idx)))])) &&& E)))
                (pure (ovsf)))
            else (pure (ovsf)) ) : SailM (BitVec 64) )
          if ((((! is_hyp) && (! include_lo_name)) || (is_hyp && (! include_hi_name))) : Bool)
          then
            (do
              ArmFull.assert ((0 ≤b idx) && (idx <b 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:4619.64-4619.65"
              let ovsf : (BitVec 64) := (BitVec.update ovsf (Sail.Int.toNatChecked (idx)) (Bit 0#1))
              (pure (ovsf)))
          else (pure (ovsf))
      (pure loop_vars)) ) : SailM (BitVec 64) )
  let ovsf : (BitVec 64) :=
    if ((exclude_cyc || (! include_lo_name)) : Bool)
    then (BitVec.update ovsf CYCLE_COUNTER_ID (Bit 0#1))
    else ovsf
  let ovsf ← (( do
    if (check_e : Bool)
    then
      (do
        let w__11 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
        let ovsf :=
          ((BitVec.update ovsf CYCLE_COUNTER_ID
            (Bit
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ovsf CYCLE_COUNTER_ID)])) &&& (_get_PMCR_EL0_Type_E
                  w__11)))) : (BitVec 64))
        (pure (ovsf)))
    else (pure (ovsf)) ) : SailM (BitVec 64) )
  let w__14 ← (( do
    if ((← do
         (HaveAArch64 ())) : Bool)
    then
      (do
        (HavePMUv3ICNTR ()))
    else (pure false) ) : SailM Bool )
  let ovsf ← (( do
    if (w__14 : Bool)
    then
      (do
        let ovsf : (BitVec 64) :=
          if ((! include_lo_name) : Bool)
          then (BitVec.update ovsf INSTRUCTION_COUNTER_ID (Bit 0#1))
          else ovsf
        if (check_e : Bool)
        then
          (do
            let w__15 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
            let ovsf :=
              ((BitVec.update ovsf INSTRUCTION_COUNTER_ID
                (Bit
                  ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ovsf INSTRUCTION_COUNTER_ID)])) &&& (_get_PMCR_EL0_Type_E
                      w__15)))) : (BitVec 64))
            (pure (ovsf)))
        else (pure (ovsf)))
    else (pure (ovsf)) ) : SailM (BitVec 64) )
  let ovsf ← (( do
    if (check_cnten : Bool)
    then
      (do
        let w__16 ← (( do (HaveAArch64 ()) ) : SailM Bool )
        let cnten ← (( do
          if (w__16 : Bool)
          then
            (do
              readReg PMCNTENCLR_EL0)
          else
            (do
              let w__18 ← (( do (PMCNTENCLR_read ()) ) : SailM (BitVec 32) )
              (pure ((Sail.BitVec.zeroExtend w__18 64)))) ) : SailM (BitVec 64) )
        let ovsf : (BitVec 64) := (ovsf &&& cnten)
        (pure (ovsf)))
    else (pure (ovsf)) ) : SailM (BitVec 64) )
  let ovsf ← (( do
    if (check_inten : Bool)
    then
      (do
        let w__19 ← (( do (HaveAArch64 ()) ) : SailM Bool )
        let inten ← (( do
          if (w__19 : Bool)
          then
            (do
              readReg PMINTENCLR_EL1)
          else
            (do
              let w__21 ← (( do (PMINTENCLR_read ()) ) : SailM (BitVec 32) )
              (pure ((Sail.BitVec.zeroExtend w__21 64)))) ) : SailM (BitVec 64) )
        let ovsf : (BitVec 64) := (ovsf &&& inten)
        (pure (ovsf)))
    else (pure (ovsf)) ) : SailM (BitVec 64) )
  (pure ((! (IsZero ovsf))))


def ELIsInHost (el : (BitVec 2)) : SailM Bool := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveVirtHostExt ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        (ELUsingAArch32 EL2)) ) : SailM Bool )
  if (w__2 : Bool)
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
              if ((← do
                   (EL2Enabled ())) : Bool)
              then
                (do
                  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_E2H w__4) == 1#1) : Bool))))
              else (pure false))
          else
            (do
              if ((questionMark == EL1) : Bool)
              then (pure (false))
              else
                (do
                  if ((questionMark == EL0) : Bool)
                  then
                    (do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__7) +++ (_get_HCR_EL2_Type_TGE w__8)) == 0b11#2) : Bool))))
                      else (pure false))
                  else
                    (do
                      (Unreachable ())
                      (undefined_bool_at (← occLabel 563) ()))))))


def ProfilingBufferEnabled (_ : Unit) : SailM Bool := do
  let owning_el ← (( do (undefined_bitvector_at (← occLabel 586) 2) ) : SailM (BitVec 2) )
  let owning_ss ← (( do (undefined_SecurityState (← occLabel 587) ()) ) : SailM SecurityState )
  let w__0 ← (( do (HaveStatisticalProfiling ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let w__1 ← (( do (ProfilingBufferOwner ()) ) : SailM (SecurityState × (BitVec 2)) )
      let (tup__0, tup__1) := (w__1 : (SecurityState × (BitVec 2)))
      let owning_ss : SecurityState := tup__0
      let owning_el : (BitVec 2) := tup__1
      let state_bits ← (( do (undefined_bitvector_at (← occLabel 588) 2) ) : SailM (BitVec 2) )
      let w__2 ← (( do (HaveRME ()) ) : SailM Bool )
      let state_bits ← (( do
        if (w__2 : Bool)
        then
          (do
            let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            let w__4 ← (( do (EffectiveSCR_EL3_NS ()) ) : SailM (BitVec 1) )
            let state_bits := (((_get_SCR_EL3_Type_NSE w__3) +++ w__4) : (BitVec 2))
            (pure (state_bits)))
        else
          (do
            let w__5 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            let state_bits := ((0#1 +++ (_get_SCR_EL3_Type_NS w__5)) : (BitVec 2))
            (pure (state_bits))) ) : SailM (BitVec 2) )
      let state_match ← (( do (undefined_bool_at (← occLabel 589) ()) ) : SailM Bool )
      let state_match : Bool :=
        match owning_ss with
        | .SS_Secure => (state_bits == 0b00#2)
        | .SS_NonSecure => (state_bits == 0b01#2)
        | .SS_Realm => (state_bits == 0b11#2)
        | _ => state_match
      if ((← do
           if ((← do
                (pure ((← do
                      let w__6 ← (( do (ELUsingAArch32 owning_el) ) : SailM Bool )
                      (pure (((! w__6) : Bool)))) && (state_match : Bool)))) : Bool)
           then
             (do
               let w__8 ← (( do readReg PMBLIMITR_EL1 ) : SailM (BitVec 64) )
               (pure ((((_get_PMBLIMITR_EL1_Type_E w__8) == 1#1) : Bool))))
           else (pure false)) : Bool)
      then
        (do
          let w__10 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
          (pure ((((_get_PMBSR_EL1_Type_S w__10) == 0#1) : Bool))))
      else (pure false))


/-- Type quantifiers: k_N : Nat, 4 < k_N -/
def ELFromSPSR (spsr : (BitVec k_N)) : SailM (Bool × (BitVec 2)) := do
  let el ← (( do (undefined_bitvector_at (← occLabel 631) 2) ) : SailM (BitVec 2) )
  let valid_name ← (( do (undefined_bool_at (← occLabel 632) ()) ) : SailM Bool )
  let effective_nse_ns ← (( do (undefined_bitvector_at (← occLabel 633) 2) ) : SailM (BitVec 2)
    )
  let (el, valid_name) ← (( do
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spsr 4)])) == 0#1) : Bool)
    then
      (do
        let el : (BitVec 2) := (Sail.BitVec.extractLsb spsr 3 2)
        let w__0 ← (( do (EffectiveSCR_EL3_NSE ()) ) : SailM (BitVec 1) )
        let w__1 ← (( do (EffectiveSCR_EL3_NS ()) ) : SailM (BitVec 1) )
        let effective_nse_ns : (BitVec 2) := (w__0 +++ w__1)
        let w__2 ← (( do (HaveAArch64 ()) ) : SailM Bool )
        let valid_name ← (( do
          if ((! w__2) : Bool)
          then (pure (false))
          else
            (do
              if ((! (HaveEL el)) : Bool)
              then (pure (false))
              else
                (do
                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spsr 1)])) == 1#1) : Bool)
                  then (pure (false))
                  else
                    (do
                      if (((el == EL0) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spsr 0)])) == 1#1)) : Bool)
                      then (pure (false))
                      else
                        (do
                          let w__5 ← (( do
                            (pure ((← do
                                  (pure ((← do
                                        (HaveRME ())) && ((el != EL3) : Bool)))) && ((effective_nse_ns == 0b10#2) : Bool)))
                            ) : SailM Bool )
                          if (w__5 : Bool)
                          then (pure (false))
                          else
                            (do
                              let w__9 ← (( do
                                if ((← do
                                     if ((((el == EL2) && (HaveEL EL3)) : Bool) : Bool)
                                     then
                                       (do
                                         let w__6 ← (( do (IsSecureEL2Enabled ()) ) : SailM Bool )
                                         (pure (((! w__6) : Bool))))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__8 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                    (pure ((((_get_SCR_EL3_Type_NS w__8) == 0#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              let valid_name : Bool :=
                                if (w__9 : Bool)
                                then false
                                else true
                              (pure (valid_name))))))) ) : SailM Bool )
        (pure ((el, valid_name))))
    else
      (do
        if ((HaveAArch32 ()) : Bool)
        then
          (do
            let w__10 ← (( do (ELFromM32 (Sail.BitVec.extractLsb spsr 4 0)) ) : SailM
              (Bool × (BitVec 2)) )
            let (tup__0, tup__1) := (w__10 : (Bool × (BitVec 2)))
            let valid_name : Bool := tup__0
            let el : (BitVec 2) := tup__1
            (pure ((el, valid_name))))
        else
          (let valid_name : Bool := false
          (pure ((el, valid_name))))) ) : SailM ((BitVec 2) × Bool) )
  let el ← (( do
    if ((! valid_name) : Bool)
    then
      (do
        (__UNKNOWN_bits 2))
    else (pure (el)) ) : SailM (BitVec 2) )
  let el := el
  (pure ((valid_name, el)))


def AArch32_WriteMode (mode : (BitVec 5)) : SailM Unit := do
  let el ← (( do (undefined_bitvector_at (← occLabel 643) 2) ) : SailM (BitVec 2) )
  let valid_name ← (( do (undefined_bool_at (← occLabel 644) ()) ) : SailM Bool )
  let w__0 ← (( do (ELFromM32 mode) ) : SailM (Bool × (BitVec 2)) )
  let (tup__0, tup__1) := (w__0 : (Bool × (BitVec 2)))
  let valid_name : Bool := tup__0
  let el : (BitVec 2) := tup__1
  ArmFull.assert valid_name "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:8277.21-8277.22"
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__1 with M := mode }
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__2 with EL := el }
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__3 with nRW := 1#1 }
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__4 with SP := if (((mode == M32_User) || (mode == M32_System)) : Bool)
    then 0#1
    else 1#1 }


def AArch32_GenerateDebugExceptionsFrom (from_el : (BitVec 2)) (from_state : SecurityState) : SailM Bool := do
  let mask ← (( do (undefined_bitvector_at (← occLabel 652) 1) ) : SailM (BitVec 1) )
  let spd ← (( do (undefined_bitvector_at (← occLabel 653) 2) ) : SailM (BitVec 2) )
  let w__0 ← (( do (DebugTargetFrom from_state) ) : SailM (BitVec 2) )
  let w__1 ← (( do (ELUsingAArch32 w__0) ) : SailM Bool )
  if ((! w__1) : Bool)
  then
    (do
      let mask : (BitVec 1) := 0#1
      (AArch64_GenerateDebugExceptionsFrom from_el from_state mask))
  else
    (do
      let w__7 ← (( do
        if ((← do
             if ((← do
                  let w__3 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
                  (pure ((((_get_DBGOSLSR_Type_OSLK w__3) == 1#1) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 (DoubleLockStatus ()))) : Bool)
        then (pure true)
        else
          (do
            (Halted ())) ) : SailM Bool )
      if (w__7 : Bool)
      then (pure (false))
      else
        (do
          let enabled ← (( do (undefined_bool_at (← occLabel 654) ()) ) : SailM Bool )
          if (((HaveEL EL3) && (BEq.beq from_state SS_Secure)) : Bool)
          then
            (do
              ArmFull.assert (from_el != EL2) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:8448.29-8448.30"
              let w__8 ← (( do (IsSecureEL2Enabled ()) ) : SailM Bool )
              let enabled ← (( do
                if (w__8 : Bool)
                then
                  (do
                    let w__9 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                    let enabled := (((_get_MDCR_EL3_Type_SDD w__9) == 0#1) : Bool)
                    (pure (enabled)))
                else
                  (do
                    let w__10 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                    let spd ← (( do
                      if (w__10 : Bool)
                      then
                        (do
                          let w__11 ← (( do readReg SDCR ) : SailM (BitVec 32) )
                          (pure ((_get_SDCR_Type_SPD w__11))))
                      else
                        (do
                          let w__12 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                          (pure ((_get_MDCR_EL3_Type_SPD32 w__12)))) ) : SailM (BitVec 2) )
                    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spd 1)])) == 1#1) : Bool)
                    then
                      (let enabled : Bool :=
                        ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access spd 0)])) == 1#1)
                      (pure (enabled)))
                    else
                      (do
                        (AArch32_SelfHostedSecurePrivilegedInvasiveDebugEnabled ()))) ) : SailM Bool
                )
              if ((from_el == EL0) : Bool)
              then
                (do
                  if ((enabled : Bool) : Bool)
                  then (pure true)
                  else
                    (do
                      let w__14 ← (( do (SDER_read ()) ) : SailM (BitVec 32) )
                      (pure ((((_get_SDER_Type_SUIDEN w__14) == 1#1) : Bool)))))
              else (pure (enabled)))
          else
            (let enabled : Bool := (from_el != EL2)
            (pure (enabled)))))


def AArch64_MaybeZeroRegisterUppers (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  ArmFull.assert w__0 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:8991.25-8991.26"
  let first : Int := 0
  let last : Int := 14
  let include_R15_name ← (( do (undefined_bool_at (← occLabel 670) ()) ) : SailM Bool )
  let w__3 ← (( do
    if ((← do
         let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__1.EL == EL0) : Bool)))) : Bool)
    then
      (do
        let w__2 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
        (pure (((! w__2) : Bool))))
    else (pure false) ) : SailM Bool )
  let (first, include_R15_name, last) ← (( do
    if (w__3 : Bool)
    then
      (let first : Int := 0
      let last : Int := 14
      let include_R15_name : Bool := false
      (pure ((first, include_R15_name, last))))
    else
      (do
        let w__10 ← (( do
          if ((← do
               if ((← do
                    if ((← do
                         let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
                         (pure (((w__4.EL == EL0) : Bool)))) : Bool)
                    then (pure true)
                    else
                      (do
                        let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__5.EL == EL1) : Bool))))) : Bool)
               then
                 (do
                   (EL2Enabled ()))
               else (pure false)) : Bool)
          then
            (do
              let w__9 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
              (pure (((! w__9) : Bool))))
          else (pure false) ) : SailM Bool )
        let (first, include_R15_name, last) : (Int × Bool × Int) :=
          if (w__10 : Bool)
          then
            (let first : Int := 0
            let last : Int := 30
            let include_R15_name : Bool := false
            (first, include_R15_name, last))
          else
            (let first : Int := 0
            let last : Int := 30
            let include_R15_name : Bool := true
            (first, include_R15_name, last))
        (pure ((first, include_R15_name, last)))) ) : SailM (Int × Bool × Int) )
  let last : Int := last
  let first : Int := first
  let loop_n_lower : Int := first
  let loop_n_upper : Int := last
  (do
    let mut loop_vars := ()
    for n in [loop_n_lower:loop_n_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__12 ← (( do
          if ((((n != 15) || include_R15_name) : Bool) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_ZEROUPPER))
          else (pure false) ) : SailM Bool )
        if (w__12 : Bool)
        then
          (do
            (set_R_bits (Sail.Int.toNatChecked (n)) 63 32 (Zeros (n := 32))))
        else (pure (()))
    (pure loop_vars))


end ArmFull.Functions
