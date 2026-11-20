module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0010
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0017
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0025
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0035
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0086
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0124
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0151
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0179
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0183
public import ArmFull.Fn.M0185
public import ArmFull.Fn.M0187 set_option backward.proofsInPublic true @[expose] public section

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

def getISR (_ : Unit) : SailM (BitVec 32) := do
  let fiq_nmi ← (( do (undefined_bool_at (← occLabel 2890) ()) ) : SailM Bool )
  let fiq_pending ← (( do (undefined_bool_at (← occLabel 2891) ()) ) : SailM Bool )
  let irq_nmi ← (( do (undefined_bool_at (← occLabel 2892) ()) ) : SailM Bool )
  let irq_pending ← (( do (undefined_bool_at (← occLabel 2893) ()) ) : SailM Bool )
  let value_name : (BitVec 32) := (Zeros (n := 32))
  let value_name : (BitVec 32) :=
    (BitVec.update value_name 8
      (Bit
        (if ((IsPhysicalSErrorPending ()) : Bool)
        then 1#1
        else 0#1)))
  let w__0 ← (( do (IRQPending ()) ) : SailM (Bool × Bool) )
  let (tup__0, tup__1) := (w__0 : (Bool × Bool))
  let irq_pending : Bool := tup__0
  let irq_nmi : Bool := tup__1
  let (tup__0, tup__1) := ((FIQPending ()) : (Bool × Bool))
  let fiq_pending : Bool := tup__0
  let fiq_nmi : Bool := tup__1
  let w__3 ← (( do
    if ((← do
         (HaveFeatNMI ())) : Bool)
    then
      (do
        let w__2 ← (( do (UsingAArch32 ()) ) : SailM Bool )
        (pure (((! w__2) : Bool))))
    else (pure false) ) : SailM Bool )
  let value_name : (BitVec 32) :=
    if (w__3 : Bool)
    then
      (let value_name : (BitVec 32) :=
        (BitVec.update value_name 10
          (Bit
            (if ((irq_pending && irq_nmi) : Bool)
            then 1#1
            else 0#1)))
      (BitVec.update value_name 9
        (Bit
          (if ((fiq_pending && fiq_nmi) : Bool)
          then 1#1
          else 0#1))))
    else value_name
  let value_name : (BitVec 32) :=
    (BitVec.update value_name 7
      (Bit
        (if (irq_pending : Bool)
        then 1#1
        else 0#1)))
  let value_name : (BitVec 32) :=
    (BitVec.update value_name 6
      (Bit
        (if (fiq_pending : Bool)
        then 1#1
        else 0#1)))
  let w__8 ← (( do
    if ((← do
         if ((← do
              let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__4.EL == EL1) : Bool)))) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_TGE w__7) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__8 : Bool)
  then
    (do
      let w__13 ← (( do
        if ((← do
             if ((← do
                  (HaveFeatNMI ())) : Bool)
             then
               (do
                 let w__10 ← (( do (UsingAArch32 ()) ) : SailM Bool )
                 (pure (((! w__10) : Bool))))
             else (pure false)) : Bool)
        then
          (do
            (IsHCRXEL2Enabled ()))
        else (pure false) ) : SailM Bool )
      let value_name ← (( do
        if (w__13 : Bool)
        then
          (do
            let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            let value_name ← (( do
              if ((((_get_HCR_EL2_Type_IMO w__14) &&& (_get_HCR_EL2_Type_VI w__15)) == 1#1) : Bool)
              then
                (do
                  let w__16 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
                  let value_name :=
                    ((BitVec.update value_name 10 (Bit (_get_HCRX_EL2_Type_VINMI w__16))) : (BitVec 32))
                  (pure (value_name)))
              else (pure (value_name)) ) : SailM (BitVec 32) )
            let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            if ((((_get_HCR_EL2_Type_FMO w__17) &&& (_get_HCR_EL2_Type_VF w__18)) == 1#1) : Bool)
            then
              (do
                let w__19 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
                let value_name :=
                  ((BitVec.update value_name 9 (Bit (_get_HCRX_EL2_Type_VFNMI w__19))) : (BitVec 32))
                (pure (value_name)))
            else (pure (value_name)))
        else (pure (value_name)) ) : SailM (BitVec 32) )
      let w__20 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
      let value_name ← (( do
        if (((_get_HCR_EL2_Type_AMO w__20) == 1#1) : Bool)
        then
          (do
            let w__21 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            let value_name :=
              ((BitVec.update value_name 8
                (Bit
                  ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access value_name 8)])) ||| (_get_HCR_EL2_Type_VSE
                      w__21)))) : (BitVec 32))
            (pure (value_name)))
        else (pure (value_name)) ) : SailM (BitVec 32) )
      let w__22 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
      let value_name ← (( do
        if (((_get_HCR_EL2_Type_IMO w__22) == 1#1) : Bool)
        then
          (do
            let w__23 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            let value_name :=
              ((BitVec.update value_name 7 (Bit (_get_HCR_EL2_Type_VI w__23))) : (BitVec 32))
            (pure (value_name)))
        else (pure (value_name)) ) : SailM (BitVec 32) )
      let w__24 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
      if (((_get_HCR_EL2_Type_FMO w__24) == 1#1) : Bool)
      then
        (do
          let w__25 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
          let value_name :=
            ((BitVec.update value_name 6 (Bit (_get_HCR_EL2_Type_VF w__25))) : (BitVec 32))
          (pure (value_name)))
      else (pure (value_name)))
  else (pure (value_name))


def decode_aarch32_instrs_DMB_A1enc_A_txt (option_name : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (execute_aarch32_instrs_DMB_Op_A_txt option_name))
  else (pure (()))


def decode_aarch32_instrs_DMB_T1enc_A_txt (option_name : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (execute_aarch32_instrs_DMB_Op_A_txt option_name))
  else (pure (()))


def execute_aarch32_instrs_DSB_Op_A_txt (option_name : (BitVec 4)) : SailM Unit := do
  let nXS ← (( do (undefined_bool_at (← occLabel 3011) ()) ) : SailM Bool )
  let w__0 ← (( do (HaveFeatXS ()) ) : SailM Bool )
  let nXS ← (( do
    if (w__0 : Bool)
    then
      (do
        if ((← do
             if ((← do
                  if ((← do
                       if ((← do
                            let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
                            (pure (((w__1.EL == EL0) : Bool)))) : Bool)
                       then (pure true)
                       else
                         (do
                           let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                           (pure (((w__2.EL == EL1) : Bool))))) : Bool)
                  then
                    (do
                      let w__4 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__4) : Bool))))
                  else (pure false)) : Bool)
             then
               (do
                 (IsHCRXEL2Enabled ()))
             else (pure false)) : Bool)
        then
          (do
            let w__8 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCRX_EL2_Type_FnXS w__8) == 1#1) : Bool))))
        else (pure false))
    else (pure (false)) ) : SailM Bool )
  let domain ← (( do (undefined_MBReqDomain (← occLabel 3012) ()) ) : SailM MBReqDomain )
  let types ← (( do (undefined_MBReqTypes (← occLabel 3013) ()) ) : SailM MBReqTypes )
  let (domain, types) ← (( do
    match option_name with
    | 0b0001 =>
      (let domain : MBReqDomain := MBReqDomain_OuterShareable
      let types : MBReqTypes := MBReqTypes_Reads
      (pure ((domain, types))))
    | 0b0010 =>
      (let domain : MBReqDomain := MBReqDomain_OuterShareable
      let types : MBReqTypes := MBReqTypes_Writes
      (pure ((domain, types))))
    | 0b0011 =>
      (let domain : MBReqDomain := MBReqDomain_OuterShareable
      let types : MBReqTypes := MBReqTypes_All
      (pure ((domain, types))))
    | 0b0101 =>
      (let domain : MBReqDomain := MBReqDomain_Nonshareable
      let types : MBReqTypes := MBReqTypes_Reads
      (pure ((domain, types))))
    | 0b0110 =>
      (let domain : MBReqDomain := MBReqDomain_Nonshareable
      let types : MBReqTypes := MBReqTypes_Writes
      (pure ((domain, types))))
    | 0b0111 =>
      (let domain : MBReqDomain := MBReqDomain_Nonshareable
      let types : MBReqTypes := MBReqTypes_All
      (pure ((domain, types))))
    | 0b1001 =>
      (let domain : MBReqDomain := MBReqDomain_InnerShareable
      let types : MBReqTypes := MBReqTypes_Reads
      (pure ((domain, types))))
    | 0b1010 =>
      (let domain : MBReqDomain := MBReqDomain_InnerShareable
      let types : MBReqTypes := MBReqTypes_Writes
      (pure ((domain, types))))
    | 0b1011 =>
      (let domain : MBReqDomain := MBReqDomain_InnerShareable
      let types : MBReqTypes := MBReqTypes_All
      (pure ((domain, types))))
    | 0b1101 =>
      (let domain : MBReqDomain := MBReqDomain_FullSystem
      let types : MBReqTypes := MBReqTypes_Reads
      (pure ((domain, types))))
    | 0b1110 =>
      (let domain : MBReqDomain := MBReqDomain_FullSystem
      let types : MBReqTypes := MBReqTypes_Writes
      (pure ((domain, types))))
    | _ =>
      (do
        let b__0 := option_name
        ArmFull.assert (! (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 3 3)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                   b__0 1 0)) == (0b00#2 : (BitVec 2)))) : Bool)
          then true
          else false : Bool)) "sail-inputs/14-instrs32.sail:3029.20-3029.21"
        let domain : MBReqDomain := MBReqDomain_FullSystem
        let types : MBReqTypes := MBReqTypes_All
        (pure ((domain, types)))) ) : SailM (MBReqDomain × MBReqTypes) )
  let types := types
  let w__14 ← (( do
    if ((← do
         if ((← do
              let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__10.EL == EL0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__11.EL == EL1) : Bool))))) : Bool)
    then
      (do
        (EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let domain ← (( do
    if (w__14 : Bool)
    then
      (do
        let w__15 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
        let domain : MBReqDomain :=
          if (((_get_HCR_Type_BSU w__15) == 0b11#2) : Bool)
          then MBReqDomain_FullSystem
          else domain
        let w__17 ← (( do
          (pure ((← do
                let w__16 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                (pure ((((_get_HCR_Type_BSU w__16) == 0b10#2) : Bool)))) && ((bne domain
                MBReqDomain_FullSystem) : Bool))) ) : SailM Bool )
        let domain : MBReqDomain :=
          if (w__17 : Bool)
          then MBReqDomain_OuterShareable
          else domain
        let w__19 ← (( do
          (pure ((← do
                let w__18 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                (pure ((((_get_HCR_Type_BSU w__18) == 0b01#2) : Bool)))) && ((BEq.beq domain
                MBReqDomain_Nonshareable) : Bool))) ) : SailM Bool )
        let domain : MBReqDomain :=
          if (w__19 : Bool)
          then MBReqDomain_InnerShareable
          else domain
        (pure (domain)))
    else (pure (domain)) ) : SailM MBReqDomain )
  (DataSynchronizationBarrier domain types nXS)


def execute_aarch64_instrs_system_tme_tcommit (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (IsTMEEnabled ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__1 ← (( do readReg TSTATE ) : SailM TMState )
  if ((w__1.depth == 0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__2 ← (( do readReg TSTATE ) : SailM TMState )
  let _ : Unit :=
    if ((w__2.depth == 1) : Bool)
    then
      (let _ : Unit := (CommitTransactionalWrites ())
      (ClearExclusiveLocal (ProcessorID ())))
    else ()
  let w__3 ← (( do readReg TSTATE ) : SailM TMState )
  let w__4 ← (( do readReg TSTATE ) : SailM TMState )
  writeReg TSTATE { w__3 with depth := (w__4.depth -i 1) }


/-- Type quantifiers: t : Nat, 0 ≤ t ∧ t ≤ 31 -/
def execute_aarch64_instrs_system_tme_ttest (t : Nat) : SailM Unit := do
  let w__0 ← (( do (IsTMEEnabled ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__1 ← (( do readReg TSTATE ) : SailM TMState )
  (X_set t 64 (integer_subrange w__1.depth 63 0))


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
  ArmFull.assert w__2 "sail-inputs/03-v8_base.sail:4945.108-4945.109"
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
        ArmFull.assert w__3 "sail-inputs/03-v8_base.sail:4954.30-4954.31"
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
                ArmFull.assert ((0 ≤b idx) && (idx <b 32)) "sail-inputs/03-v8_base.sail:4973.56-4973.57"
                if (((E == 1#1) : Bool) : Bool)
                then
                  (do
                    let w__25 ← (( do (PMCNTENSET_read ()) ) : SailM (BitVec 32) )
                    (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__25 idx)])) == 1#1) : Bool))))
                else (pure false)))) ) : SailM Bool )
  let prohibited : Bool := false
  let w__28 ← (( do
    (pure ((← do
          (HaveEL EL3)) && ((BEq.beq ss SS_Secure) : Bool))) ) : SailM Bool )
  let prohibited ← (( do
    if (w__28 : Bool)
    then
      (do
        let w__29 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
        let prohibited ← (( do
          if ((! w__29) : Bool)
          then
            (do
              if ((← do
                   if ((← do
                        let w__30 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                        (pure ((((_get_MDCR_EL3_Type_SPME w__30) == 0#1) : Bool)))) : Bool)
                   then
                     (do
                       (HavePMUv3p7 ()))
                   else (pure false)) : Bool)
              then
                (do
                  let w__33 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                  (pure ((((_get_MDCR_EL3_Type_MPMX w__33) == 0#1) : Bool))))
              else (pure false))
          else
            (do
              let w__35 ← (( do readReg SDCR ) : SailM (BitVec 32) )
              let prohibited := (((_get_SDCR_Type_SPME w__35) == 0#1) : Bool)
              (pure (prohibited))) ) : SailM Bool )
        let w__37 ← (( do
          if ((prohibited : Bool) : Bool)
          then
            (do
              let w__36 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__36.EL == EL0) : Bool))))
          else (pure false) ) : SailM Bool )
        if (w__37 : Bool)
        then
          (do
            let w__38 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
            if (w__38 : Bool)
            then
              (do
                let w__39 ← (( do (SDER_read ()) ) : SailM (BitVec 32) )
                let prohibited := (((_get_SDER_Type_SUNIDEN w__39) == 0#1) : Bool)
                (pure (prohibited)))
            else
              (do
                let w__40 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                if (w__40 : Bool)
                then
                  (do
                    let w__41 ← (( do (SDER32_EL3_read ()) ) : SailM (BitVec 64) )
                    let prohibited := (((_get_SDER32_EL3_Type_SUNIDEN w__41) == 0#1) : Bool)
                    (pure (prohibited)))
                else (pure (prohibited))))
        else (pure (prohibited)))
    else (pure (prohibited)) ) : SailM Bool )
  let w__47 ← (( do
    if ((← do
         if ((← do
              if (((! prohibited) : Bool) : Bool)
              then
                (do
                  (HavePMUv3p7 ()))
              else (pure false)) : Bool)
         then
           (do
             let w__44 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__44.EL == EL3) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        (HaveAArch64 ()))
    else (pure false) ) : SailM Bool )
  let prohibited ← (( do
    if (w__47 : Bool)
    then
      (do
        if ((← do
             let w__48 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
             (pure ((((_get_MDCR_EL3_Type_MPMX w__48) == 1#1) : Bool)))) : Bool)
        then
          (pure ((← do
                let w__49 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                (pure ((((_get_MDCR_EL3_Type_SPME w__49) == 0#1) : Bool)))) || (! resvd_for_el2)))
        else (pure false))
    else (pure (prohibited)) ) : SailM Bool )
  let w__56 ← (( do
    (pure ((← do
          if ((← do
               if (((! prohibited) : Bool) : Bool)
               then
                 (do
                   let w__52 ← (( do readReg PSTATE ) : SailM ProcState )
                   (pure (((w__52.EL == EL2) : Bool))))
               else (pure false)) : Bool)
          then
            (do
              (HaveHPMDExt ()))
          else (pure false)) && (! resvd_for_el2))) ) : SailM Bool )
  let prohibited ← (( do
    if (w__56 : Bool)
    then
      (do
        let w__57 ← (( do (HaveAArch64 ()) ) : SailM Bool )
        let hpmd ← (( do
          if (w__57 : Bool)
          then
            (do
              let w__58 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_MDCR_EL2_Type_HPMD w__58))))
          else
            (do
              let w__59 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
              (pure ((_get_HDCR_Type_HPMD w__59)))) ) : SailM (BitVec 1) )
        let prohibited : Bool := (hpmd == 1#1)
        (pure (prohibited)))
    else (pure (prohibited)) ) : SailM Bool )
  let w__61 ← (( do
    if ((prohibited : Bool) : Bool)
    then
      (do
        let w__60 ← (( do (HaveNoSecurePMUDisableOverride ()) ) : SailM Bool )
        (pure (((! w__60) : Bool))))
    else (pure false) ) : SailM Bool )
  let prohibited ← (( do
    if (w__61 : Bool)
    then
      (do
        let w__62 ← (( do (ExternalSecureNoninvasiveDebugEnabled ()) ) : SailM Bool )
        let prohibited := ((! w__62) : Bool)
        (pure (prohibited)))
    else (pure (prohibited)) ) : SailM Bool )
  let frozen : Bool := false
  let w__63 ← (( do (HavePMUv3p7 ()) ) : SailM Bool )
  let frozen ← (( do
    if (w__63 : Bool)
    then
      (do
        let FZ ← (( do (undefined_bitvector_at (← occLabel 537) 1) ) : SailM (BitVec 1) )
        let FZ ← (( do
          if (resvd_for_el2 : Bool)
          then
            (do
              let w__64 ← (( do (HaveAArch64 ()) ) : SailM Bool )
              if (w__64 : Bool)
              then
                (do
                  let w__65 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_MDCR_EL2_Type_HPMFZO w__65))))
              else
                (do
                  let w__66 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                  (pure ((_get_HDCR_Type_HPMFZO w__66)))))
          else
            (do
              let w__68 ← (( do (HaveAArch64 ()) ) : SailM Bool )
              if (w__68 : Bool)
              then
                (do
                  let w__69 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
                  (pure ((_get_PMCR_EL0_Type_FZO w__69))))
              else
                (do
                  let w__70 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
                  (pure ((_get_PMCR_Type_FZO w__70))))) ) : SailM (BitVec 1) )
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
        let w__74 ← (( do (HaveAArch64 ()) ) : SailM Bool )
        let dp ← (( do
          if (w__74 : Bool)
          then
            (do
              let w__75 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
              (pure ((_get_PMCR_EL0_Type_DP w__75))))
          else
            (do
              let w__76 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
              (pure ((_get_PMCR_Type_DP w__76)))) ) : SailM (BitVec 1) )
        let enabled : Bool := (enabled && (dp == 0#1))
        let prohibited : Bool := false
        let frozen : Bool := false
        (pure ((enabled, frozen, prohibited))))
    else (pure ((enabled, frozen, prohibited))) ) : SailM (Bool × Bool × Bool) )
  let w__78 ← (( do
    (pure ((← do
          (HavePMUv3p5 ())) && ((idx == CYCLE_COUNTER_ID) : Bool))) ) : SailM Bool )
  let prohibited ← (( do
    if (w__78 : Bool)
    then
      (do
        let w__80 ← (( do
          (pure ((← do
                (HaveEL EL3)) && ((BEq.beq ss SS_Secure) : Bool))) ) : SailM Bool )
        let prohibited ← (( do
          if (w__80 : Bool)
          then
            (do
              let w__81 ← (( do (HaveAArch64 ()) ) : SailM Bool )
              let sccd ← (( do
                if (w__81 : Bool)
                then
                  (do
                    let w__82 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                    (pure ((_get_MDCR_EL3_Type_SCCD w__82))))
                else
                  (do
                    let w__83 ← (( do readReg SDCR ) : SailM (BitVec 32) )
                    (pure ((_get_SDCR_Type_SCCD w__83)))) ) : SailM (BitVec 1) )
              let prohibited : Bool :=
                if ((sccd == 1#1) : Bool)
                then true
                else prohibited
              (pure (prohibited)))
          else (pure (prohibited)) ) : SailM Bool )
        let w__84 ← (( do readReg PSTATE ) : SailM ProcState )
        if ((w__84.EL == EL2) : Bool)
        then
          (do
            let w__85 ← (( do (HaveAArch64 ()) ) : SailM Bool )
            let hccd ← (( do
              if (w__85 : Bool)
              then
                (do
                  let w__86 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_MDCR_EL2_Type_HCCD w__86))))
              else
                (do
                  let w__87 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                  (pure ((_get_HDCR_Type_HCCD w__87)))) ) : SailM (BitVec 1) )
            let prohibited : Bool :=
              if ((hccd == 1#1) : Bool)
              then true
              else prohibited
            (pure (prohibited)))
        else (pure (prohibited)))
    else (pure (prohibited)) ) : SailM Bool )
  let w__89 ← (( do
    (pure ((← do
          (HavePMUv3p7 ())) && ((idx == CYCLE_COUNTER_ID) : Bool))) ) : SailM Bool )
  let prohibited ← (( do
    if (w__89 : Bool)
    then
      (do
        let w__94 ← (( do
          if ((← do
               if ((← do
                    let w__90 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__90.EL == EL3) : Bool)))) : Bool)
               then
                 (do
                   (HaveAArch64 ()))
               else (pure false)) : Bool)
          then
            (do
              let w__93 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
              (pure ((((_get_MDCR_EL3_Type_MCCD w__93) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let prohibited : Bool :=
          if (w__94 : Bool)
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
        let w__95 ← (( do readReg PMICFILTR_EL0 ) : SailM (BitVec 64) )
        let filter := ((Sail.BitVec.extractLsb w__95 31 0) : (BitVec 32))
        (pure (filter)))
    else
      (do
        if ((questionMark == CYCLE_COUNTER_ID) : Bool)
        then
          (do
            let w__96 ← (( do (HaveAArch64 ()) ) : SailM Bool )
            if (w__96 : Bool)
            then
              (do
                let w__97 ← (( do readReg PMCCFILTR_EL0 ) : SailM (BitVec 64) )
                (pure ((Sail.BitVec.extractLsb w__97 31 0))))
            else
              (do
                (PMCCFILTR_read ())))
        else
          (do
            let w__100 ← (( do (HaveAArch64 ()) ) : SailM Bool )
            if (w__100 : Bool)
            then
              (do
                ArmFull.assert ((0 ≤b idx) && (idx <b 32)) "sail-inputs/03-v8_base.sail:5058.56-5058.57"
                let w__101 ← (( do readReg PMEVTYPER_EL0 ) : SailM (Vector (BitVec 64) 32) )
                (pure ((Sail.BitVec.extractLsb (GetElem?.getElem! w__101 idx) 31 0))))
            else
              (do
                ArmFull.assert ((0 ≤b idx) && (idx <b 31)) "sail-inputs/03-v8_base.sail:5061.56-5061.57"
                (PMEVTYPER_read idx)))) ) : SailM (BitVec 32) )
  let filter := filter
  let P : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 31)]))
  let U : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 30)]))
  let w__104 ← (( do (HaveEL EL3) ) : SailM Bool )
  let NSK : (BitVec 1) :=
    if (w__104 : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 29)]))
    else 0#1
  let w__105 ← (( do (HaveEL EL3) ) : SailM Bool )
  let NSU : (BitVec 1) :=
    if (w__105 : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 28)]))
    else 0#1
  let w__106 ← (( do (HaveEL EL2) ) : SailM Bool )
  let NSH : (BitVec 1) :=
    if (w__106 : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 27)]))
    else 0#1
  let w__109 ← (( do
    if ((← do
         (HaveEL EL3)) : Bool)
    then
      (do
        (HaveAArch64 ()))
    else (pure false) ) : SailM Bool )
  let M : (BitVec 1) :=
    if (w__109 : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 26)]))
    else 0#1
  let w__112 ← (( do
    if ((← do
         (HaveEL EL3)) : Bool)
    then
      (do
        (HaveSecureEL2Ext ()))
    else (pure false) ) : SailM Bool )
  let SH : (BitVec 1) :=
    if (w__112 : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 24)]))
    else 0#1
  let w__113 ← (( do (HaveRME ()) ) : SailM Bool )
  let RLK : (BitVec 1) :=
    if (w__113 : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 22)]))
    else 0#1
  let w__114 ← (( do (HaveRME ()) ) : SailM Bool )
  let RLU : (BitVec 1) :=
    if (w__114 : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 21)]))
    else 0#1
  let w__115 ← (( do (HaveRME ()) ) : SailM Bool )
  let RLH : (BitVec 1) :=
    if (w__115 : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access filter 20)]))
    else 0#1
  let ss ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
  let w__116 ← (( do readReg PSTATE ) : SailM ProcState )
  let questionMark := w__116.EL
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
                    let w__117 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                    let filtered : Bool :=
                      if (w__117 : Bool)
                      then (M != P)
                      else (P == 1#1)
                    (pure (filtered)))
                else (pure (filtered))))) ) : SailM Bool )
  (pure ((((((! debug) && enabled) && (! prohibited)) && (! filtered)) && (! frozen))))


end ArmFull.Functions
