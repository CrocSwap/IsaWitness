module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0010
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0018
public import ArmFull.Fn.M0020
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0035
public import ArmFull.Fn.M0040
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0043
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0048
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0086
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0120
public import ArmFull.Fn.M0121
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0153
public import ArmFull.Fn.M0159
public import ArmFull.Fn.M0167
public import ArmFull.Fn.M0172
public import ArmFull.Fn.M0175
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0180
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0183
public import ArmFull.Fn.M0184
public import ArmFull.Fn.M0194
public import ArmFull.Fn.M0195
public import ArmFull.Fn.M0199
public import ArmFull.Fn.M0216
public import ArmFull.Fn.M0218
public import ArmFull.Fn.M0225
public import ArmFull.Fn.M0226
public import ArmFull.Fn.M0227
public import ArmFull.Fn.M0239
public import ArmFull.Fn.M0240
public import ArmFull.Fn.M0241 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: k_cold_reset : Bool -/
def AArch64_TakeReset (cold_reset : Bool) : SailM Unit := do
  let w__0 ← (( do (HaveAArch64 ()) ) : SailM Bool )
  ArmFull.assert w__0 "sail-inputs/03-v8_base.sail:33509.24-33509.25"
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__1 with nRW := 0#1 }
  let w__2 ← (( do (HaveEL EL3) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with EL := EL3 })
  else
    (do
      let w__4 ← (( do (HaveEL EL2) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__5 with EL := EL2 })
      else
        (do
          let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__6 with EL := EL1 }))
  (AArch64_ResetControlRegisters cold_reset)
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with SP := 1#1 }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with D := (Sail.BitVec.extractLsb 0b1111#4 3 3) }
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__9 with A := (Sail.BitVec.extractLsb 0b1111#4 2 2) }
  let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__10 with I := (Sail.BitVec.extractLsb 0b1111#4 1 1) }
  let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__11 with F := (Sail.BitVec.extractLsb 0b1111#4 0 0) }
  let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__12 with SS := 0#1 }
  let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__13 with DIT := 0#1 }
  let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__14 with IL := 0#1 }
  let w__15 ← (( do (HaveTME ()) ) : SailM Bool )
  if (w__15 : Bool)
  then
    (do
      let w__16 ← (( do readReg TSTATE ) : SailM TMState )
      writeReg TSTATE { w__16 with depth := 0 })
  else (pure (()))
  (AArch64_ResetGeneralRegisters ())
  (AArch64_ResetSIMDFPRegisters ())
  (AArch64_ResetSpecialRegisters ())
  (ResetExternalDebugRegisters cold_reset)
  let rv ← (( do (undefined_bitvector_at (← occLabel 2401) 64) ) : SailM (BitVec 64) )
  let w__17 ← (( do (HaveEL EL3) ) : SailM Bool )
  let rv ← (( do
    if (w__17 : Bool)
    then
      (do
        readReg RVBAR_EL3)
    else
      (do
        let w__19 ← (( do (HaveEL EL2) ) : SailM Bool )
        if (w__19 : Bool)
        then
          (do
            readReg RVBAR_EL2)
        else
          (do
            readReg RVBAR_EL1)) ) : SailM (BitVec 64) )
  let w__23 ← (( do
    (pure ((← do
          let w__22 ← (( do (AArch64_PAMax ()) ) : SailM Int )
          (pure (((is_zero_subrange rv 63 w__22) : Bool)))) && ((IsZero
          (Sail.BitVec.extractLsb rv 1 0)) : Bool))) ) : SailM Bool )
  ArmFull.assert w__23 "sail-inputs/03-v8_base.sail:33539.73-33539.74"
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
      let pl2_match ← (( do
        (pure ((← do
              (HaveEL EL2)) && ((((hmc == 1#1) && ((ssc +++ pxc) != 0b1000#4)) || (ssc == 0b11#2)) : Bool)))
        ) : SailME Bool Bool )
      let pl1_match : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access pxc 0)])) == 1#1)
      let pl0_match : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access pxc 1)])) == 1#1)
      let ssu_match : Bool := (((isbreakpnt && (hmc == 0#1)) && (pxc == 0b00#2)) && (ssc != 0b11#2))
      let priv_match ← (( do (undefined_bool_at (← occLabel 2657) ()) ) : SailME Bool Bool )
      let priv_match ← (( do
        if (ssu_match : Bool)
        then
          (do
            if ((← do
                 let w__1 ← (( do readReg PSTATE ) : SailME Bool ProcState )
                 (pure (((w__1.M == M32_User) : Bool)))) : Bool)
            then (pure true)
            else
              (do
                if ((← do
                     let w__2 ← (( do readReg PSTATE ) : SailME Bool ProcState )
                     (pure (((w__2.M == M32_Svc) : Bool)))) : Bool)
                then (pure true)
                else
                  (do
                    let w__3 ← (( do readReg PSTATE ) : SailME Bool ProcState )
                    (pure (((w__3.M == M32_System) : Bool))))))
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
            let w__6 ← (( do (IsContextMatchingBreakpoint linked_n) ) : SailME Bool Bool )
            let (linked, linked_n) ← (( do
              if ((! w__6) : Bool)
              then
                (do
                  let w__7 ← (( do (ContextMatchingBreakpointRange ()) ) : SailME Bool
                    (Int × Int) )
                  let (tup__0, tup__1) := (w__7 : (Int × Int))
                  let first_ctx_cmp : Int := tup__0
                  let last_ctx_cmp : Int := tup__1
                  let last_ctx_cmp : Int := last_ctx_cmp
                  let first_ctx_cmp : Int := first_ctx_cmp
                  let w__8 ← (( do
                    (ConstrainUnpredictableInteger first_ctx_cmp last_ctx_cmp
                      Unpredictable_BPNOTCTXCMP) ) : SailME Bool (Constraint × Int) )
                  let (tup__0, tup__1) := (w__8 : (Constraint × Int))
                  let c : Constraint := tup__0
                  let linked_n : Int := tup__1
                  ArmFull.assert ((BEq.beq c Constraint_DISABLED) || ((BEq.beq c Constraint_NONE) || (BEq.beq
                        c Constraint_UNKNOWN))) "sail-inputs/03-v8_base.sail:40427.92-40427.93"
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
  ArmFull.assert (BEq.beq w__0 InstrSet_T32) "sail-inputs/03-v8_base.sail:42428.44-42428.45"
  let address : (BitVec 32) := (BitVec.update address 0 (Bit 0#1))
  let branch_conditional : Bool := true
  (BranchTo address BranchType_DIR branch_conditional)


/-- Type quantifiers: k_cold_reset : Bool -/
def AArch32_TakeReset (cold_reset : Bool) : SailM Unit := do
  let w__0 ← (( do (HaveAArch64 ()) ) : SailM Bool )
  ArmFull.assert (! w__0) "sail-inputs/03-v8_base.sail:42845.34-42845.35"
  let w__1 ← (( do (HaveEL EL3) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      (AArch32_WriteMode M32_Svc)
      let w__2 ← (( do readReg SCR ) : SailM (BitVec 32) )
      writeReg SCR (Sail.BitVec.updateSubrange w__2 0 0 0#1))
  else
    (do
      let w__3 ← (( do (HaveEL EL2) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          (AArch32_WriteMode M32_Hyp))
      else
        (do
          (AArch32_WriteMode M32_Svc)))
  (AArch32_ResetControlRegisters cold_reset)
  let w__4 ← (( do (FPEXC_read ()) ) : SailM (BitVec 32) )
  (FPEXC_write (_update_FPEXC_Type_EN w__4 0#1))
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with A := (Sail.BitVec.extractLsb 0b111#3 2 2) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with I := (Sail.BitVec.extractLsb 0b111#3 1 1) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with F := (Sail.BitVec.extractLsb 0b111#3 0 0) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with IT := 0b00000000#8 }
  let w__11 ← (( do
    if ((← do
         (HaveEL EL2)) : Bool)
    then
      (do
        let w__10 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__10) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__11 : Bool)
  then
    (do
      let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__13 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
      writeReg PSTATE { w__12 with T := (_get_HSCTLR_Type_TE w__13) }
      let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__15 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
      writeReg PSTATE { w__14 with E := (_get_HSCTLR_Type_EE w__15) })
  else
    (do
      let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__17 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
      writeReg PSTATE { w__16 with T := (_get_SCTLR_Type_TE w__17) }
      let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__19 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
      writeReg PSTATE { w__18 with E := (_get_SCTLR_Type_EE w__19) })
  let w__20 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__20 with IL := 0#1 }
  (AArch32_ResetGeneralRegisters ())
  (AArch32_ResetSIMDFPRegisters ())
  (AArch32_ResetSpecialRegisters ())
  (ResetExternalDebugRegisters cold_reset)
  let rv ← (( do (undefined_bitvector_at (← occLabel 2773) 32) ) : SailM (BitVec 32) )
  let w__21 ← (( do (HaveEL EL3) ) : SailM Bool )
  let rv ← (( do
    if (w__21 : Bool)
    then
      (do
        let w__22 ← (( do readReg MVBAR ) : SailM (BitVec 32) )
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__22 0)])) == 1#1) : Bool)
        then
          (do
            let w__23 ← (( do readReg MVBAR ) : SailM (BitVec 32) )
            let rv := (((Sail.BitVec.extractLsb w__23 31 1) +++ 0#1) : (BitVec 32))
            (pure (rv)))
        else
          (do
            (__IMPDEF_bits 32 "reset vector address")))
    else
      (do
        let w__25 ← (( do readReg RVBAR ) : SailM (BitVec 32) )
        let rv := (((Sail.BitVec.extractLsb w__25 31 1) +++ 0#1) : (BitVec 32))
        (pure (rv))) ) : SailM (BitVec 32) )
  let w__28 ← (( do
    if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rv 0)])) == 0#1) : Bool) : Bool)
    then
      (do
        (pure ((← do
              let w__26 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__26.T == 1#1) : Bool)))) || (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                  rv 1)])) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__28 "sail-inputs/03-v8_base.sail:42880.62-42880.63"
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


def execute_aarch64_instrs_branch_unconditional_dret (_ : Unit) : SailM Unit := do
  (DRPSInstruction ())


def execute_aarch64_instrs_system_barriers_isb (_ : Unit) : SailM Unit := do
  (InstructionSynchronizationBarrier ())
  let w__2 ← (( do
    if ((← do
         (HaveBRBExt ())) : Bool)
    then
      (do
        (BRBEBranchOnISB ()))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (BRBEISB ()))
  else (pure (()))
  let w__3 ← (( do (HaveStatisticalProfiling ()) ) : SailM Bool )
  if (w__3 : Bool)
  then
    (do
      (SPEISB ()))
  else (pure (()))


/-- Type quantifiers: bit_pos : Nat, datasize : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ bit_pos ∧ bit_pos ≤ 63 -/
def execute_aarch64_instrs_branch_conditional_test (bit_pos : Nat) (bit_val : (BitVec 1)) (datasize : Nat) (offset : (BitVec 64)) (t : Nat) : SailM Unit := do
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (X_read t datasize)) ) : SailM
    (BitVec datasize) )
  let branch_conditional : Bool := true
  ArmFull.assert (bit_pos <b datasize) "sail-inputs/15-instrs64.sail:52130.43-52130.44"
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand bit_pos)])) == bit_val) : Bool)
  then
    (do
      let w__0 ← (( do (PC_read ()) ) : SailM (BitVec 64) )
      (BranchTo (w__0 + offset) BranchType_DIR branch_conditional))
  else
    (do
      (BranchNotTaken BranchType_DIR branch_conditional))


/-- Type quantifiers: d : Nat, k_data : Bool, 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_strip_dp_1src (d : Nat) (data : Bool) : SailM Unit := do
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
      let w__2 ← (( do (Strip w__1 data) ) : SailM (BitVec 64) )
      (X_set d 64 w__2))
  else (pure (()))


/-- Type quantifiers: k_retry : Bool -/
def FailTransaction (cause : TMFailure) (retry : Bool) : SailM Unit := do
  (FailTransaction__1 cause retry false (Zeros (n := 15)))


/-- Type quantifiers: size : Nat, size > 0 -/
def PhysMemRead (desc : AddressDescriptor) (size : Nat) (accdesc : AccessDescriptor) (translation_info : (Option TranslationInfo)) : SailM (PhysMemRetStatus × (BitVec (8 * size))) := do
  let paddress := desc.paddress.address
  if (((size ≥b 4) && ((Sail.BitVec.castWidth (m := 40) (Sail.BitVec.extractLsb paddress
           (Sail.Int.toNatChecked (((Sail.BitVec.length paddress) -i 1))) 16)) == (Sail.BitVec.castWidth (m := 40) (ZeroExtend1
           (m := (Sail.Int.toNatChecked ((((56 -i 1) -i 16) +i 1)))) GIC_BASE)))) : Bool)
  then
    (do
      let w__0 ← (( do (__ReadGIC (Sail.BitVec.extractLsb paddress 15 0)) ) : SailM (BitVec 32) )
      (pure (((CreatePhysMemRetStatus Fault_None), (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend
          w__0 (Sail.Int.toNatChecked ((8 *i size)))))))))
  else
    (do
      if (((Sail.BitVec.castWidth (m := 40) (Sail.BitVec.extractLsb paddress
             (Sail.Int.toNatChecked (((Sail.BitVec.length paddress) -i 1))) 16)) == (Sail.BitVec.castWidth (m := 40) (ZeroExtend1
             (m := (Sail.Int.toNatChecked ((((56 -i 1) -i 16) +i 1)))) UART_BASE))) : Bool)
      then
        (pure (((CreatePhysMemRetStatus Fault_None), (Sail.BitVec.castWidth (__ReadUART
            (Sail.BitVec.extractLsb paddress 15 0) size)))))
      else
        (do
          let w__1 ← (( do
            (sail_mem_read
              (read_request accdesc translation_info size desc.vaddress desc.paddress.address)) ) :
            SailM (Result ((BitVec (8 * size)) × (Option Bool)) Fault) )
          let w__2 : (PhysMemRetStatus × (BitVec (8 * size))) :=
            match w__1 with
            | .Ok (value, _) => ((CreatePhysMemRetStatus Fault_None), value)
            | .Err statuscode =>
              ((CreatePhysMemRetStatus statuscode), (Sail.BitVec.castWidth (BitVec.zero
                (Sail.Int.toNatChecked ((8 *i size))))))
          (pure (w__2))))


/-- Type quantifiers: n : Nat, size : Int, 0 ≤ n ∧ n < 64 -/
def AArch64_BreakpointMatch (n : Nat) (vaddress : (BitVec 64)) (accdesc : AccessDescriptor) (size : Int) : SailM (Bool × Bool) := do
  let match_i ← (( do (undefined_bool_at (← occLabel 1389) ()) ) : SailM Bool )
  let valid_mismatch_name ← (( do (undefined_bool_at (← occLabel 1390) ()) ) : SailM Bool )
  let value_match_name ← (( do (undefined_bool_at (← occLabel 1391) ()) ) : SailM Bool )
  let w__0 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
  let w__1 ← (( do (ELUsingAArch32 w__0) ) : SailM Bool )
  ArmFull.assert (! w__1) "sail-inputs/03-v8_base.sail:23613.61-23613.62"
  let w__2 ← (( do (NumBreakpointsImplemented ()) ) : SailM Int )
  ArmFull.assert (n <b w__2) "sail-inputs/03-v8_base.sail:23614.42-23614.43"
  let linking_enabled ← (( do
    if ((← do
         let w__3 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
         let b__1 := (_get_DBGBCR_EL1_Type_BT (GetElem?.getElem! w__3 n))
         (pure ((if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 3 3)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                    b__1 1 0)) == (0b11#2 : (BitVec 2)))) : Bool)
           then true
           else
             (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 3 3)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                      b__1 0 0)) == (1#1 : (BitVec 1)))) : Bool)
             then true
             else false) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             (HaveFeatABLE ())) : Bool)
        then
          (do
            let w__5 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
            (pure ((((_get_DBGBCR_EL1_Type_BT2 (GetElem?.getElem! w__5 n)) == 1#1) : Bool))))
        else (pure false)) ) : SailM Bool )
  if (linking_enabled : Bool)
  then (pure ((false, false)))
  else
    (do
      let enabled ← (( do (IsBreakpointEnabled n) ) : SailM Bool )
      let w__7 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
      let b__0 := (_get_DBGBCR_EL1_Type_BT (GetElem?.getElem! w__7 n))
      let linked : Bool :=
        (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 3 3)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                 b__0 1 0)) == (0b01#2 : (BitVec 2)))) : Bool)
        then true
        else false : Bool)
      let isbreakpnt : Bool := true
      let linked_to : Bool := false
      let w__8 ← (( do (Havev8p9Debug ()) ) : SailM Bool )
      let lbnx ← (( do
        if (w__8 : Bool)
        then
          (do
            let w__9 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
            (pure ((_get_DBGBCR_EL1_Type_LBNX (GetElem?.getElem! w__9 n)))))
        else (pure (0b00#2)) ) : SailM (BitVec 2) )
      let w__10 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
      let linked_n : Int :=
        (BitVec.toNat (lbnx +++ (_get_DBGBCR_EL1_Type_LBN (GetElem?.getElem! w__10 n))))
      let w__11 ← (( do (HaveRME ()) ) : SailM Bool )
      let ssce ← (( do
        if (w__11 : Bool)
        then
          (do
            let w__12 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
            (pure ((_get_DBGBCR_EL1_Type_SSCE (GetElem?.getElem! w__12 n)))))
        else (pure (0#1)) ) : SailM (BitVec 1) )
      let w__13 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
      let w__14 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
      let w__15 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
      let state_match ← (( do
        (AArch64_StateMatch (_get_DBGBCR_EL1_Type_SSC (GetElem?.getElem! w__13 n)) ssce
          (_get_DBGBCR_EL1_Type_HMC (GetElem?.getElem! w__14 n))
          (_get_DBGBCR_EL1_Type_PMC (GetElem?.getElem! w__15 n)) linked linked_n isbreakpnt vaddress
          accdesc) ) : SailM Bool )
      let w__16 ← (( do (AArch64_BreakpointValueMatch n vaddress linked_to isbreakpnt) ) : SailM
        (Bool × Bool) )
      let (tup__0, tup__1) := (w__16 : (Bool × Bool))
      let value_match_name : Bool := tup__0
      let valid_mismatch_name : Bool := tup__1
      let w__18 ← (( do
        (pure ((← do
              (HaveAArch32 ())) && ((size == 4) : Bool))) ) : SailM Bool )
      let value_match_name ← (( do
        if (w__18 : Bool)
        then
          (do
            let (__tup_0, _) ← (( do
              (AArch64_BreakpointValueMatch n (BitVec.addInt vaddress 2) linked_to isbreakpnt) ) :
              SailM (Bool × Bool) )
            let match_i : Bool := __tup_0
            if (((! value_match_name) && match_i) : Bool)
            then
              (do
                (ConstrainUnpredictableBool Unpredictable_BPMATCHHALF))
            else (pure (value_match_name)))
        else (pure (value_match_name)) ) : SailM Bool )
      let w__21 ← (( do
        if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access vaddress 1)])) == 1#1) : Bool) : Bool)
        then
          (do
            let w__20 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
            (pure ((((_get_DBGBCR_EL1_Type_BAS (GetElem?.getElem! w__20 n)) == 0b1111#4) : Bool))))
        else (pure false) ) : SailM Bool )
      let value_match_name ← (( do
        if (w__21 : Bool)
        then
          (do
            if (value_match_name : Bool)
            then
              (do
                (ConstrainUnpredictableBool Unpredictable_BPMATCHHALF))
            else (pure (value_match_name)))
        else (pure (value_match_name)) ) : SailM Bool )
      let val_match : Bool := ((value_match_name && state_match) && enabled)
      let is_mismatch : Bool := ((valid_mismatch_name && state_match) && enabled)
      (pure ((val_match, is_mismatch))))


end ArmFull.Functions
