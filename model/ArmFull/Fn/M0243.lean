import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0016
import ArmFull.Fn.M0018
import ArmFull.Fn.M0020
import ArmFull.Fn.M0023
import ArmFull.Fn.M0034
import ArmFull.Fn.M0035
import ArmFull.Fn.M0040
import ArmFull.Fn.M0041
import ArmFull.Fn.M0043
import ArmFull.Fn.M0044
import ArmFull.Fn.M0047
import ArmFull.Fn.M0048
import ArmFull.Fn.M0049
import ArmFull.Fn.M0087
import ArmFull.Fn.M0100
import ArmFull.Fn.M0117
import ArmFull.Fn.M0120
import ArmFull.Fn.M0121
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0150
import ArmFull.Fn.M0155
import ArmFull.Fn.M0166
import ArmFull.Fn.M0174
import ArmFull.Fn.M0180
import ArmFull.Fn.M0182
import ArmFull.Fn.M0183
import ArmFull.Fn.M0185
import ArmFull.Fn.M0194
import ArmFull.Fn.M0195
import ArmFull.Fn.M0196
import ArmFull.Fn.M0200
import ArmFull.Fn.M0219
import ArmFull.Fn.M0226
import ArmFull.Fn.M0227
import ArmFull.Fn.M0228
import ArmFull.Fn.M0236
import ArmFull.Fn.M0240
import ArmFull.Fn.M0241
import ArmFull.Fn.M0242

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

/-- Type quantifiers: k_interrupt : Bool, k_retry : Bool -/
def FailTransaction__1 (cause : TMFailure) (retry : Bool) (interrupt : Bool) (reason : (BitVec 15)) : SailM Unit := do
  ArmFull.assert ((! retry) || (! interrupt)) "sail-arm/v8_base.sail:7577.48-7577.49"
  let w__3 ← (( do
    if ((← do
         (HaveBRBExt ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (BranchRecordAllowed w__1.EL))
    else (pure false) ) : SailM Bool )
  if (w__3 : Bool)
  then
    (do
      let w__4 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__4 6 6 1#1))
  else (pure (()))
  let _ : Unit := (DiscardTransactionalWrites ())
  if ((bne cause TMFailure_TRIVIAL) : Bool)
  then
    (do
      (RestoreTransactionCheckpoint ()))
  else (pure (()))
  let _ : Unit := (ClearExclusiveLocal (ProcessorID ()))
  let result : (BitVec 64) := (Zeros (n := 64))
  let result : (BitVec 64) :=
    (BitVec.update result 23
      (Bit
        (if (interrupt : Bool)
        then 1#1
        else 0#1)))
  let result : (BitVec 64) :=
    (BitVec.update result 15
      (Bit
        (if ((retry && (! interrupt)) : Bool)
        then 1#1
        else 0#1)))
  let result : (BitVec 64) :=
    match cause with
    | .TMFailure_TRIVIAL => (BitVec.update result 24 (Bit 1#1))
    | .TMFailure_DBG => (BitVec.update result 22 (Bit 1#1))
    | .TMFailure_NEST => (BitVec.update result 21 (Bit 1#1))
    | .TMFailure_SIZE => (BitVec.update result 20 (Bit 1#1))
    | .TMFailure_ERR => (BitVec.update result 19 (Bit 1#1))
    | .TMFailure_IMP => (BitVec.update result 18 (Bit 1#1))
    | .TMFailure_MEM => (BitVec.update result 17 (Bit 1#1))
    | .TMFailure_CNCL =>
      (let result : (BitVec 64) := (BitVec.update result 16 (Bit 1#1))
      (Sail.BitVec.updateSubrange result 14 0 reason))
  let w__5 ← (( do readReg TSTATE ) : SailM TMState )
  writeReg TSTATE { w__5 with depth := 0 }
  let w__6 ← (( do readReg TSTATE ) : SailM TMState )
  (X_set w__6.Rt 64 result)
  let branch_conditional : Bool := false
  let w__7 ← (( do readReg TSTATE ) : SailM TMState )
  (BranchTo w__7.nPC BranchType_TMFAIL branch_conditional)
  (EndOfInstruction ())


def __ReadGIC (offset : (BitVec 16)) : SailM (BitVec 32) := do
  match offset with
  | 0x1004 => (pure (__GICD_TYPER))
  | 0x1800 => (pure (0xFFFFFFFF#32))
  | 0x1C04 =>
    (do
      let w__0 ← (( do (gic_read_ram 0x1C04#16) ) : SailM (BitVec 32) )
      let _ : Unit := (prerr_bits "[GIC] Read 1C04: " w__0)
      (gic_read_ram 0x1C04#16))
  | 0x2000 =>
    (do
      let w__2 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
      let _ : Unit := (prerr_bits "[GIC] Read GICC_CTLR " w__2)
      readReg GICC_CTLR)
  | 0x200C =>
    (do
      let intid ← (( do (__GIC_AcknowledgeInterrupt ()) ) : SailM (BitVec 32) )
      let _ : Unit := (prerr_bits "[GIC] Acknowledged interrupt " intid)
      (pure (intid)))
  | 0x20FC => (pure (__GICC_IIDR))
  | _ =>
    (let _ : Unit := (prerr_bits "[GIC] Read offset: " offset)
    (pure ((Zeros (n := 32)))))


/-- Type quantifiers: k_isbreakpnt : Bool, k_linked_in : Bool, linked_n_in : Int -/
def AArch64_StateMatch (ssc_in : (BitVec 2)) (ssce_in : (BitVec 1)) (hmc_in : (BitVec 1)) (pxc_in : (BitVec 2)) (linked_in : Bool) (linked_n_in : Int) (isbreakpnt : Bool) (vaddress : (BitVec 64)) (accdesc : AccessDescriptor) : SailM Bool := SailME.run do
  let first_ctx_cmp ← (( do (undefined_int_at (← occLabel 1383) ()) ) : SailME Bool Int )
  let last_ctx_cmp ← (( do (undefined_int_at (← occLabel 1384) ()) ) : SailME Bool Int )
  let linked_to ← (( do (undefined_bool_at (← occLabel 1385) ()) ) : SailME Bool Bool )
  let w__0 ← (( do (HaveRME ()) ) : SailME Bool Bool )
  if ((! w__0) : Bool)
  then
    (do
      ArmFull.assert (ssce_in == 0#1) "sail-arm/v8_base.sail:23515.29-23515.30")
  else (pure (()))
  let ssc : (BitVec 2) := ssc_in
  let ssce : (BitVec 1) := ssce_in
  let hmc : (BitVec 1) := hmc_in
  let pxc : (BitVec 2) := pxc_in
  let linked : Bool := linked_in
  let linked_n : Int := linked_n_in
  let c ← (( do (undefined_Constraint (← occLabel 1386) ()) ) : SailME Bool Constraint )
  let w__1 ← (( do (CheckValidStateMatch ssc ssce hmc pxc isbreakpnt) ) : SailME Bool
    (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) )
  let (tup__0, tup__1, tup__2, tup__3, tup__4) :=
    (w__1 : (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)))
  let c : Constraint := tup__0
  let ssc : (BitVec 2) := tup__1
  let ssce : (BitVec 1) := tup__2
  let hmc : (BitVec 1) := tup__3
  let pxc : (BitVec 2) := tup__4
  if ((BEq.beq c Constraint_DISABLED) : Bool)
  then (pure (false))
  else
    (do
      let EL3_match : Bool :=
        (((HaveEL EL3) && (hmc == 1#1)) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ssc 0)])) == 0#1))
      let EL2_match : Bool :=
        ((HaveEL EL2) && (((hmc == 1#1) && ((ssc +++ pxc) != 0b1000#4)) || (ssc == 0b11#2)))
      let EL1_match : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access pxc 0)])) == 1#1)
      let EL0_match : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access pxc 1)])) == 1#1)
      let priv_match ← (( do (undefined_bool_at (← occLabel 1387) ()) ) : SailME Bool Bool )
      let questionMark := accdesc.el
      let priv_match : Bool :=
        if ((questionMark == EL3) : Bool)
        then EL3_match
        else
          (if ((questionMark == EL2) : Bool)
          then EL2_match
          else
            (if ((questionMark == EL1) : Bool)
            then EL1_match
            else
              (if ((questionMark == EL0) : Bool)
              then EL0_match
              else priv_match)))
      let ss_match ← (( do (undefined_bool_at (← occLabel 1388) ()) ) : SailME Bool Bool )
      let ss_match : Bool :=
        match (BitVec.setWidth 3 (ssce +++ ssc)) with
        | 0b000 => ((hmc == 1#1) || (bne accdesc.ss SS_Root))
        | 0b001 => (BEq.beq accdesc.ss SS_NonSecure)
        | 0b010 =>
          (((hmc == 1#1) && (BEq.beq accdesc.ss SS_Root)) || (BEq.beq accdesc.ss SS_Secure))
        | 0b011 => (((hmc == 1#1) && (bne accdesc.ss SS_Root)) || (BEq.beq accdesc.ss SS_Secure))
        | 0b101 => (BEq.beq accdesc.ss SS_Realm)
        | _ => ss_match
      let linked_match : Bool := false
      let is_linked_mismatch : Bool := false
      let (linked, linked_n) ← (( do
        if (linked : Bool)
        then
          (do
            let w__2 ← (( do (IsContextMatchingBreakpoint linked_n) ) : SailME Bool Bool )
            if ((! w__2) : Bool)
            then
              (do
                let w__3 ← (( do (ContextMatchingBreakpointRange ()) ) : SailME Bool (Int × Int)
                  )
                let (tup__0, tup__1) := (w__3 : (Int × Int))
                let first_ctx_cmp : Int := tup__0
                let last_ctx_cmp : Int := tup__1
                let last_ctx_cmp : Int := last_ctx_cmp
                let first_ctx_cmp : Int := first_ctx_cmp
                let w__4 ← (( do
                  (ConstrainUnpredictableInteger first_ctx_cmp last_ctx_cmp
                    Unpredictable_BPNOTCTXCMP) ) : SailME Bool (Constraint × Int) )
                let (tup__0, tup__1) := (w__4 : (Constraint × Int))
                let c : Constraint := tup__0
                let linked_n : Int := tup__1
                ArmFull.assert ((BEq.beq c Constraint_DISABLED) || ((BEq.beq c Constraint_NONE) || (BEq.beq
                      c Constraint_UNKNOWN))) "sail-arm/v8_base.sail:23575.92-23575.93"
                let linked ← (( do
                  match c with
                  | .Constraint_DISABLED =>
                    (do
                      SailME.throw (false : Bool)
                      (pure (linked)))
                  | .Constraint_NONE => (pure (false))
                  | _ => (pure (linked)) ) : SailME Bool Bool )
                (pure ((linked, linked_n))))
            else (pure ((linked, linked_n))))
        else (pure ((linked, linked_n))) ) : SailME Bool (Bool × Int) )
      let linked_n : Int := linked_n
      let (is_linked_mismatch, linked_match) ← (( do
        if (linked : Bool)
        then
          (do
            let linked_to : Bool := true
            let w__5 ← (( do (AArch64_BreakpointValueMatch linked_n vaddress linked_to isbreakpnt)
              ) : SailME Bool (Bool × Bool) )
            let (tup__0, tup__1) := (w__5 : (Bool × Bool))
            let linked_match : Bool := tup__0
            let is_linked_mismatch : Bool := tup__1
            (pure ((is_linked_mismatch, linked_match))))
        else (pure ((is_linked_mismatch, linked_match))) ) : SailME Bool (Bool × Bool) )
      (pure (((priv_match && ss_match) && (((! linked) || ((! is_linked_mismatch) && linked_match)) || (is_linked_mismatch && (! linked_match)))))))


/-- Type quantifiers: k_cold_reset : Bool -/
def AArch64_TakeReset (cold_reset : Bool) : SailM Unit := do
  let w__0 ← (( do (HaveAArch64 ()) ) : SailM Bool )
  ArmFull.assert w__0 "sail-arm/v8_base.sail:33499.24-33499.25"
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__1 with nRW := 0#1 }
  if ((HaveEL EL3) : Bool)
  then
    (do
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with EL := EL3 })
  else
    (do
      if ((HaveEL EL2) : Bool)
      then
        (do
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__3 with EL := EL2 })
      else
        (do
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__4 with EL := EL1 }))
  (AArch64_ResetControlRegisters cold_reset)
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with SP := 1#1 }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with D := (Sail.BitVec.extractLsb 0b1111#4 3 3) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with A := (Sail.BitVec.extractLsb 0b1111#4 2 2) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with I := (Sail.BitVec.extractLsb 0b1111#4 1 1) }
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__9 with F := (Sail.BitVec.extractLsb 0b1111#4 0 0) }
  let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__10 with SS := 0#1 }
  let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__11 with DIT := 0#1 }
  let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__12 with IL := 0#1 }
  let w__13 ← (( do (HaveTME ()) ) : SailM Bool )
  if (w__13 : Bool)
  then
    (do
      let w__14 ← (( do readReg TSTATE ) : SailM TMState )
      writeReg TSTATE { w__14 with depth := 0 })
  else (pure (()))
  (AArch64_ResetGeneralRegisters ())
  (AArch64_ResetSIMDFPRegisters ())
  (AArch64_ResetSpecialRegisters ())
  (ResetExternalDebugRegisters cold_reset)
  let rv ← (( do (undefined_bitvector_at (← occLabel 2401) 64) ) : SailM (BitVec 64) )
  let rv ← (( do
    if ((HaveEL EL3) : Bool)
    then
      (do
        readReg RVBAR_EL3)
    else
      (do
        if ((HaveEL EL2) : Bool)
        then
          (do
            readReg RVBAR_EL2)
        else
          (do
            readReg RVBAR_EL1)) ) : SailM (BitVec 64) )
  let w__19 ← (( do
    (pure ((← do
          let w__18 ← (( do (AArch64_PAMax ()) ) : SailM Int )
          (pure (((is_zero_subrange rv 63 w__18) : Bool)))) && ((IsZero
          (Sail.BitVec.extractLsb rv 1 0)) : Bool))) ) : SailM Bool )
  ArmFull.assert w__19 "sail-arm/v8_base.sail:33529.73-33529.74"
  let branch_conditional : Bool := false
  (BranchTo rv BranchType_RESET branch_conditional)


def SPEPreExecution (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (StatisticalProfilingEnabled ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (PMUEvent PMU_EVENT_SAMPLE_POP)
      let w__1 ← (( do (SPEToCollectSample ()) ) : SailM Bool )
      if (w__1 : Bool)
      then
        (do
          let w__2 ← (( do readReg SPESampleInFlight ) : SailM Bool )
          if ((! w__2) : Bool)
          then
            (do
              writeReg SPESampleInFlight true
              (SPEStartCounter SPECounterPosTotalLatency)
              (SPEStartCounter SPECounterPosIssueLatency)
              (SPESampleAddContext ())
              (SPESampleAddAddressPCVirtual ())
              (SPESampleAddTimeStamp ()))
          else
            (do
              (PMUEvent PMU_EVENT_SAMPLE_COLLISION)
              let w__3 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
              writeReg PMBSR_EL1 (Sail.BitVec.updateSubrange w__3 16 16 1#1))
          (SPESampleAddOpOther__1 false))
      else (pure (())))
  else (pure (()))


/-- Type quantifiers: k_isbreakpnt : Bool, k_linked_in : Bool, linked_n_in : Int -/
def AArch32_StateMatch (ssc_in : (BitVec 2)) (hmc_in : (BitVec 1)) (pxc_in : (BitVec 2)) (linked_in : Bool) (linked_n_in : Int) (isbreakpnt : Bool) (accdesc : AccessDescriptor) : SailM Bool := SailME.run do
  let first_ctx_cmp ← (( do (undefined_int_at (← occLabel 2652) ()) ) : SailME Bool Int )
  let last_ctx_cmp ← (( do (undefined_int_at (← occLabel 2653) ()) ) : SailME Bool Int )
  let linked_to ← (( do (undefined_bool_at (← occLabel 2654) ()) ) : SailME Bool Bool )
  let vaddress ← (( do (undefined_bitvector_at (← occLabel 2655) 32) ) : SailME Bool (BitVec 32)
    )
  let hmc : (BitVec 1) := hmc_in
  let ssc : (BitVec 2) := ssc_in
  let pxc : (BitVec 2) := pxc_in
  let linked : Bool := linked_in
  let linked_n : Int := linked_n_in
  let c ← (( do (undefined_Constraint (← occLabel 2656) ()) ) : SailME Bool Constraint )
  let (__tup_0, __tup_1, _, __tup_3, __tup_4) ← (( do
    (CheckValidStateMatch ssc 0#1 hmc pxc isbreakpnt) ) : SailME Bool
    (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) )
  let c : Constraint := __tup_0
  let ssc : (BitVec 2) := __tup_1
  let hmc : (BitVec 1) := __tup_3
  let pxc : (BitVec 2) := __tup_4
  if ((BEq.beq c Constraint_DISABLED) : Bool)
  then (pure (false))
  else
    (do
      let pl2_match : Bool :=
        ((HaveEL EL2) && (((hmc == 1#1) && ((ssc +++ pxc) != 0b1000#4)) || (ssc == 0b11#2)))
      let pl1_match : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access pxc 0)])) == 1#1)
      let pl0_match : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access pxc 1)])) == 1#1)
      let ssu_match : Bool := (((isbreakpnt && (hmc == 0#1)) && (pxc == 0b00#2)) && (ssc != 0b11#2))
      let priv_match ← (( do (undefined_bool_at (← occLabel 2657) ()) ) : SailME Bool Bool )
      let priv_match ← (( do
        if (ssu_match : Bool)
        then
          (do
            if ((← do
                 let w__0 ← (( do readReg PSTATE ) : SailME Bool ProcState )
                 (pure (((w__0.M == M32_User) : Bool)))) : Bool)
            then (pure true)
            else
              (do
                if ((← do
                     let w__1 ← (( do readReg PSTATE ) : SailME Bool ProcState )
                     (pure (((w__1.M == M32_Svc) : Bool)))) : Bool)
                then (pure true)
                else
                  (do
                    let w__2 ← (( do readReg PSTATE ) : SailME Bool ProcState )
                    (pure (((w__2.M == M32_System) : Bool))))))
        else
          (let questionMark := accdesc.el
          let priv_match : Bool :=
            if ((questionMark == EL3) : Bool)
            then pl1_match
            else
              (if ((questionMark == EL2) : Bool)
              then pl2_match
              else
                (if ((questionMark == EL1) : Bool)
                then pl1_match
                else
                  (if ((questionMark == EL0) : Bool)
                  then pl0_match
                  else priv_match)))
          (pure (priv_match))) ) : SailME Bool Bool )
      let ss_match ← (( do (undefined_bool_at (← occLabel 2658) ()) ) : SailME Bool Bool )
      let ss_match : Bool :=
        match ssc with
        | 0b00 => true
        | 0b01 => (BEq.beq accdesc.ss SS_NonSecure)
        | 0b10 => (BEq.beq accdesc.ss SS_Secure)
        | 0b11 => ((hmc == 1#1) || (BEq.beq accdesc.ss SS_Secure))
        | _ => ss_match
      let linked_match : Bool := false
      let (linked, linked_match) ← (( do
        if (linked : Bool)
        then
          (do
            let w__5 ← (( do (IsContextMatchingBreakpoint linked_n) ) : SailME Bool Bool )
            let (linked, linked_n) ← (( do
              if ((! w__5) : Bool)
              then
                (do
                  let w__6 ← (( do (ContextMatchingBreakpointRange ()) ) : SailME Bool
                    (Int × Int) )
                  let (tup__0, tup__1) := (w__6 : (Int × Int))
                  let first_ctx_cmp : Int := tup__0
                  let last_ctx_cmp : Int := tup__1
                  let last_ctx_cmp : Int := last_ctx_cmp
                  let first_ctx_cmp : Int := first_ctx_cmp
                  let w__7 ← (( do
                    (ConstrainUnpredictableInteger first_ctx_cmp last_ctx_cmp
                      Unpredictable_BPNOTCTXCMP) ) : SailME Bool (Constraint × Int) )
                  let (tup__0, tup__1) := (w__7 : (Constraint × Int))
                  let c : Constraint := tup__0
                  let linked_n : Int := tup__1
                  ArmFull.assert ((BEq.beq c Constraint_DISABLED) || ((BEq.beq c Constraint_NONE) || (BEq.beq
                        c Constraint_UNKNOWN))) "sail-arm/v8_base.sail:40417.92-40417.93"
                  let linked ← (( do
                    match c with
                    | .Constraint_DISABLED =>
                      (do
                        SailME.throw (false : Bool)
                        (pure (linked)))
                    | .Constraint_NONE => (pure (false))
                    | _ => (pure (linked)) ) : SailME Bool Bool )
                  (pure ((linked, linked_n))))
              else (pure ((linked, linked_n))) ) : SailME Bool (Bool × Int) )
            let linked_n : Int := linked_n
            let vaddress ← (( do (__UNKNOWN_bits 32) ) : SailME Bool (BitVec 32) )
            let linked_to : Bool := true
            let (__tup_0, _) ← (( do (AArch32_BreakpointValueMatch linked_n vaddress linked_to) )
              : SailME Bool (Bool × Bool) )
            let linked_match : Bool := __tup_0
            (pure ((linked, linked_match))))
        else (pure ((linked, linked_match))) ) : SailME Bool (Bool × Bool) )
      (pure (((priv_match && ss_match) && ((! linked) || linked_match)))))


def BXWritePC (address_in : (BitVec 32)) (branch_type : BranchType) : SailM Unit := do
  let address : (BitVec 32) := address_in
  let address ← (( do
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access address 0)])) == 1#1) : Bool)
    then
      (do
        (SelectInstrSet InstrSet_T32)
        let address : (BitVec 32) := (BitVec.update address 0 (Bit 0#1))
        (pure (address)))
    else
      (do
        (SelectInstrSet InstrSet_A32)
        let w__1 ← (( do
          if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access address 1)])) == 1#1) : Bool) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_A32FORCEALIGNPC))
          else (pure false) ) : SailM Bool )
        let address : (BitVec 32) :=
          if (w__1 : Bool)
          then (BitVec.update address 1 (Bit 0#1))
          else address
        (pure (address))) ) : SailM (BitVec 32) )
  let b__0 ← (( do (AArch32_CurrentCond ()) ) : SailM (BitVec 4) )
  let branch_conditional : Bool :=
    (! (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b111#3 : (BitVec 3))) : Bool)
      then true
      else false : Bool))
  (BranchTo address branch_type branch_conditional)


def BranchWritePC (address_in : (BitVec 32)) (branch_type : BranchType) : SailM Unit := do
  let address : (BitVec 32) := address_in
  let w__0 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
  let address : (BitVec 32) :=
    if ((BEq.beq w__0 InstrSet_A32) : Bool)
    then (Sail.BitVec.updateSubrange address 1 0 0b00#2)
    else (BitVec.update address 0 (Bit 0#1))
  let b__0 ← (( do (AArch32_CurrentCond ()) ) : SailM (BitVec 4) )
  let branch_conditional : Bool :=
    (! (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b111#3 : (BitVec 3))) : Bool)
      then true
      else false : Bool))
  (BranchTo address branch_type branch_conditional)


def CBWritePC (address_in : (BitVec 32)) : SailM Unit := do
  let address : (BitVec 32) := address_in
  let w__0 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
  ArmFull.assert (BEq.beq w__0 InstrSet_T32) "sail-arm/v8_base.sail:42418.44-42418.45"
  let address : (BitVec 32) := (BitVec.update address 0 (Bit 0#1))
  let branch_conditional : Bool := true
  (BranchTo address BranchType_DIR branch_conditional)


/-- Type quantifiers: k_cold_reset : Bool -/
def AArch32_TakeReset (cold_reset : Bool) : SailM Unit := do
  let w__0 ← (( do (HaveAArch64 ()) ) : SailM Bool )
  ArmFull.assert (! w__0) "sail-arm/v8_base.sail:42835.34-42835.35"
  if ((HaveEL EL3) : Bool)
  then
    (do
      (AArch32_WriteMode M32_Svc)
      let w__1 ← (( do readReg SCR ) : SailM (BitVec 32) )
      writeReg SCR (Sail.BitVec.updateSubrange w__1 0 0 0#1))
  else
    (do
      if ((HaveEL EL2) : Bool)
      then
        (do
          (AArch32_WriteMode M32_Hyp))
      else
        (do
          (AArch32_WriteMode M32_Svc)))
  (AArch32_ResetControlRegisters cold_reset)
  let w__2 ← (( do (FPEXC_read ()) ) : SailM (BitVec 32) )
  (FPEXC_write (_update_FPEXC_Type_EN w__2 0#1))
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__3 with A := (Sail.BitVec.extractLsb 0b111#3 2 2) }
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__4 with I := (Sail.BitVec.extractLsb 0b111#3 1 1) }
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with F := (Sail.BitVec.extractLsb 0b111#3 0 0) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with IT := 0b00000000#8 }
  if (((HaveEL EL2) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__8 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
      writeReg PSTATE { w__7 with T := (_get_HSCTLR_Type_TE w__8) }
      let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__10 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
      writeReg PSTATE { w__9 with E := (_get_HSCTLR_Type_EE w__10) })
  else
    (do
      let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__12 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
      writeReg PSTATE { w__11 with T := (_get_SCTLR_Type_TE w__12) }
      let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__14 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
      writeReg PSTATE { w__13 with E := (_get_SCTLR_Type_EE w__14) })
  let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__15 with IL := 0#1 }
  (AArch32_ResetGeneralRegisters ())
  (AArch32_ResetSIMDFPRegisters ())
  (AArch32_ResetSpecialRegisters ())
  (ResetExternalDebugRegisters cold_reset)
  let rv ← (( do (undefined_bitvector_at (← occLabel 2773) 32) ) : SailM (BitVec 32) )
  let rv ← (( do
    if ((HaveEL EL3) : Bool)
    then
      (do
        let w__16 ← (( do readReg MVBAR ) : SailM (BitVec 32) )
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__16 0)])) == 1#1) : Bool)
        then
          (do
            let w__17 ← (( do readReg MVBAR ) : SailM (BitVec 32) )
            let rv := (((Sail.BitVec.extractLsb w__17 31 1) +++ 0#1) : (BitVec 32))
            (pure (rv)))
        else
          (do
            (__IMPDEF_bits 32 "reset vector address")))
    else
      (do
        let w__19 ← (( do readReg RVBAR ) : SailM (BitVec 32) )
        let rv := (((Sail.BitVec.extractLsb w__19 31 1) +++ 0#1) : (BitVec 32))
        (pure (rv))) ) : SailM (BitVec 32) )
  let w__22 ← (( do
    if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rv 0)])) == 0#1) : Bool) : Bool)
    then
      (do
        (pure ((← do
              let w__20 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__20.T == 1#1) : Bool)))) || (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                  rv 1)])) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__22 "sail-arm/v8_base.sail:42870.62-42870.63"
  let branch_conditional : Bool := false
  (BranchTo rv BranchType_RESET branch_conditional)


def execute_aarch64_instrs_branch_conditional_cond (condition : (BitVec 4)) (offset : (BitVec 64)) : SailM Unit := do
  let branch_conditional : Bool := true
  let w__0 ← (( do (ConditionHolds condition) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (PC_read ()) ) : SailM (BitVec 64) )
      (BranchTo (w__1 + offset) BranchType_DIR branch_conditional))
  else
    (do
      (BranchNotTaken BranchType_DIR branch_conditional))


def execute_aarch64_instrs_branch_conditional_hinted (condition : (BitVec 4)) (offset : (BitVec 64)) : SailM Unit := do
  let branch_conditional : Bool := true
  let w__0 ← (( do (ConditionHolds condition) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (PC_read ()) ) : SailM (BitVec 64) )
      (BranchTo (w__1 + offset) BranchType_DIR branch_conditional))
  else
    (do
      (BranchNotTaken BranchType_DIR branch_conditional))


/-- Type quantifiers: datasize : Nat, k_iszero : Bool, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧ List.elem datasize [32, 64] -/
def execute_aarch64_instrs_branch_conditional_compare (datasize : Nat) (iszero : Bool) (offset : (BitVec 64)) (t : Nat) : SailM Unit := do
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read t datasize)) ) : SailM
    (BitVec datasize) )
  let branch_conditional : Bool := true
  if (((IsZero operand1) == iszero) : Bool)
  then
    (do
      let w__0 ← (( do (PC_read ()) ) : SailM (BitVec 64) )
      (BranchTo (w__0 + offset) BranchType_DIR branch_conditional))
  else
    (do
      (BranchNotTaken BranchType_DIR branch_conditional))


def decode_dcps1_aarch64_instrs_system_exceptions_debug_exception (LL : (BitVec 2)) (imm16 : (BitVec 16)) : SailM Unit := do
  let target_level : (BitVec 2) := LL
  if ((LL == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__0 ← (( do (Halted ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_system_exceptions_debug_exception target_level)


end ArmFull.Functions
