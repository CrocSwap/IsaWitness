module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0010
public import ArmFull.Fn.M0011
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0020
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0035
public import ArmFull.Fn.M0043
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0112
public import ArmFull.Fn.M0113
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0151
public import ArmFull.Fn.M0167
public import ArmFull.Fn.M0168
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0173
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0183
public import ArmFull.Fn.M0187
public import ArmFull.Fn.M0194
public import ArmFull.Fn.M0195
public import ArmFull.Fn.M0202
public import ArmFull.Fn.M0203
public import ArmFull.Fn.M0226
public import ArmFull.Fn.M0236
public import ArmFull.Fn.M0240
public import ArmFull.Fn.M0242
public import ArmFull.Fn.M0243
public import ArmFull.Fn.M0244
public import ArmFull.Fn.M0245 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: size : Int -/
def AArch32_CheckWatchpoint (fault_in : FaultRecord) (vaddress : (BitVec 32)) (accdesc : AccessDescriptor) (size : Int) : SailM FaultRecord := SailME.run do
  let reason ← (( do (undefined_bitvector_at (← occLabel 2677) 6) ) : SailME FaultRecord
    (BitVec 6) )
  let w__0 ← (( do (S1TranslationRegime__1 ()) ) : SailME FaultRecord (BitVec 2) )
  let w__1 ← (( do (ELUsingAArch32 w__0) ) : SailME FaultRecord Bool )
  ArmFull.assert w__1 "sail-inputs/03-v8_base.sail:40767.51-40767.52"
  let fault : FaultRecord := fault_in
  if ((BEq.beq accdesc.acctype AccessType_DC) : Bool)
  then
    (do
      if ((bne accdesc.cacheop CacheOp_Invalidate) : Bool)
      then
        (do
          SailME.throw (fault : FaultRecord))
      else
        (do
          let w__2 ← (( do (__IMPDEF_boolean "DCIMVAC generates watchpoint") ) : SailME
            FaultRecord Bool )
          if ((! w__2) : Bool)
          then
            (do
              SailME.throw (fault : FaultRecord))
          else (pure (()))))
  else
    (do
      if ((! (IsDataAccess accdesc.acctype)) : Bool)
      then
        (do
          SailME.throw (fault : FaultRecord))
      else (pure (())))
  let val_match : Bool := false
  let w__3 ← (( do (NumWatchpointsImplemented ()) ) : SailME FaultRecord Int )
  let val_match ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Int := (w__3 -i 1)
    (do
      let mut loop_vars := val_match
      for i in [loop_i_lower:loop_i_upper:1]i do
        let val_match := loop_vars
        loop_vars ← do
          ArmFull.assert (i <b 16) "sail-inputs/03-v8_base.sail:40780.39-40780.40"
          let w__4 ← (( do
            (AArch32_WatchpointMatch (Sail.Int.toNatChecked (i)) vaddress size accdesc) ) : SailME
            FaultRecord Bool )
          let val_match : Bool :=
            if (w__4 : Bool)
            then true
            else val_match
          (pure (val_match))
      (pure loop_vars)) ) : SailME FaultRecord Bool )
  let w__6 ← (( do
    if ((val_match : Bool) : Bool)
    then
      (do
        (HaltOnBreakpointOrWatchpoint ()))
    else (pure false) ) : SailME FaultRecord Bool )
  if (w__6 : Bool)
  then
    (do
      let reason : (BitVec 6) := DebugHalt_Watchpoint
      writeReg EDWAR (Sail.BitVec.zeroExtend vaddress 64)
      (Halt reason)
      (pure (fault)))
  else
    (let fault : FaultRecord :=
      if (val_match : Bool)
      then
        (let fault : FaultRecord := { fault with statuscode := Fault_Debug }
        { fault with debugmoe := DebugException_Watchpoint })
      else fault
    (pure (fault)))


def decode_aarch32_instrs_HLT_A1enc_A_txt (cond : (BitVec 4)) (imm12 : (BitVec 12)) (imm4 : (BitVec 4)) : SailM Unit := do
  ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:42755.25-42755.26"
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
         (pure ((((_get_EDSCR_Type_HDE w__0) == 0#1) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaltingAllowed ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((cond != 0b1110#4) : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  (execute_aarch32_instrs_HLT_Op_A_txt ())


def decode_aarch32_instrs_HLT_T1enc_A_txt (imm6 : (BitVec 6)) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
         (pure ((((_get_EDSCR_Type_HDE w__0) == 0#1) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaltingAllowed ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch32_instrs_HLT_Op_A_txt ())


/-- Type quantifiers: vect_offset_in : Int -/
def AArch64_TakeException (target_el : (BitVec 2)) (exception_in : ExceptionRecord) (preferred_exception_return : (BitVec 64)) (vect_offset_in : Int) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         if ((← do
              (HaveEL target_el)) : Bool)
         then
           (do
             let w__1 ← (( do (ELUsingAArch32 target_el) ) : SailM Bool )
             (pure (((! w__1) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure ((((BitVec.toNat target_el) ≥b (BitVec.toNat w__3.EL)) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:10362.105-10362.106"
  let w__5 ← (( do (Halted ()) ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      (AArch64_TakeExceptionInDebugState target_el exception_in))
  else
    (do
      let except : ExceptionRecord := exception_in
      let sync_errors ← (( do (undefined_bool_at (← occLabel 716) ()) ) : SailM Bool )
      let iesb_req ← (( do (undefined_bool_at (← occLabel 717) ()) ) : SailM Bool )
      let w__6 ← (( do (HaveIESB ()) ) : SailM Bool )
      let (iesb_req, sync_errors) ← (( do
        if (w__6 : Bool)
        then
          (do
            let w__7 ← (( do (SCTLR_read target_el) ) : SailM (BitVec 64) )
            let sync_errors := (((_get_SCTLRType_IESB w__7) == 1#1) : Bool)
            let w__8 ← (( do (HaveDoubleFaultExt ()) ) : SailM Bool )
            let sync_errors ← (( do
              if (w__8 : Bool)
              then
                (do
                  if ((sync_errors : Bool) : Bool)
                  then (pure true)
                  else
                    (do
                      (pure ((← do
                            let w__9 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                            let w__10 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                            (pure (((((_get_SCR_EL3_Type_EA w__9) +++ (_get_SCR_EL3_Type_NMEA w__10)) == 0b11#2) : Bool)))) && ((target_el == EL3) : Bool)))))
              else (pure (sync_errors)) ) : SailM Bool )
            let w__14 ← (( do
              if ((sync_errors : Bool) : Bool)
              then
                (do
                  (InsertIESBBeforeException target_el))
              else (pure false) ) : SailM Bool )
            if (w__14 : Bool)
            then
              (do
                let _ : Unit := (SynchronizeErrors ())
                let iesb_req : Bool := false
                let sync_errors : Bool := false
                (TakeUnmaskedPhysicalSErrorInterrupts iesb_req)
                (pure ((iesb_req, sync_errors))))
            else (pure ((iesb_req, sync_errors))))
        else
          (let sync_errors : Bool := false
          (pure ((iesb_req, sync_errors)))) ) : SailM (Bool × Bool) )
      let w__17 ← (( do
        if ((← do
             (HaveTME ())) : Bool)
        then
          (do
            let w__16 ← (( do readReg TSTATE ) : SailM TMState )
            (pure (((w__16.depth >b 0) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__17 : Bool)
      then
        (do
          let cause ← (( do (undefined_TMFailure (← occLabel 718) ()) ) : SailM TMFailure )
          let cause : TMFailure :=
            match except.exceptype with
            | .Exception_SoftwareBreakpoint => TMFailure_DBG
            | .Exception_Breakpoint => TMFailure_DBG
            | .Exception_Watchpoint => TMFailure_DBG
            | .Exception_SoftwareStep => TMFailure_DBG
            | _ => TMFailure_ERR
          let cause := cause
          (FailTransaction cause false))
      else (pure (()))
      let _ : Unit := (SynchronizeContext ())
      let from_32 ← (( do (UsingAArch32 ()) ) : SailM Bool )
      if (from_32 : Bool)
      then
        (do
          (AArch64_MaybeZeroRegisterUppers ()))
      else (pure (()))
      let w__21 ← (( do
        if ((← if (from_32 : Bool)
             then
               (do
                 (HaveSME ()))
             else (pure false)) : Bool)
        then
          (do
            let w__20 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__20.SM == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__21 : Bool)
      then
        (do
          (ResetSVEState ()))
      else
        (do
          (MaybeZeroSVEUppers target_el))
      let vect_offset : Int := vect_offset_in
      let w__22 ← (( do readReg PSTATE ) : SailM ProcState )
      let vect_offset ← (( do
        if (((BitVec.toNat target_el) >b (BitVec.toNat w__22.EL)) : Bool)
        then
          (do
            let lower_32 ← (( do (undefined_bool_at (← occLabel 719) ()) ) : SailM Bool )
            let lower_32 ← (( do
              if ((target_el == EL3) : Bool)
              then
                (do
                  let w__23 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if (w__23 : Bool)
                  then
                    (do
                      (ELUsingAArch32 EL2))
                  else
                    (do
                      (ELUsingAArch32 EL1)))
              else
                (do
                  let w__29 ← (( do
                    (pure ((← do
                          if ((← do
                               (IsInHost ())) : Bool)
                          then
                            (do
                              let w__27 ← (( do readReg PSTATE ) : SailM ProcState )
                              (pure (((w__27.EL == EL0) : Bool))))
                          else (pure false)) && ((target_el == EL2) : Bool))) ) : SailM Bool )
                  if (w__29 : Bool)
                  then
                    (do
                      (ELUsingAArch32 EL0))
                  else
                    (do
                      (ELUsingAArch32 (BitVec.subInt target_el 1)))) ) : SailM Bool )
            let vect_offset : Int :=
              (vect_offset +i (if (lower_32 : Bool)
                then (BitVec.toNat 0x600#12)
                else (BitVec.toNat 0x400#12)))
            (pure (vect_offset)))
        else
          (do
            let w__32 ← (( do readReg PSTATE ) : SailM ProcState )
            let vect_offset : Int :=
              if ((w__32.SP == 1#1) : Bool)
              then (vect_offset +i (BitVec.toNat 0x200#12))
              else vect_offset
            (pure (vect_offset))) ) : SailM Int )
      let vect_offset : Int := vect_offset
      let spsr ← (( do (GetPSRFromPSTATE AArch64_NonDebugState 64) ) : SailM (BitVec 64) )
      let w__36 ← (( do
        if ((← do
             (pure ((← do
                   let w__33 ← (( do readReg PSTATE ) : SailM ProcState )
                   (pure (((w__33.EL == EL1) : Bool)))) && ((target_el == EL1) : Bool)))) : Bool)
        then
          (do
            (EL2Enabled ()))
        else (pure false) ) : SailM Bool )
      let spsr ← (( do
        if (w__36 : Bool)
        then
          (do
            let w__45 ← (( do
              if ((← do
                   (HaveNV2Ext ())) : Bool)
              then
                (do
                  if ((← do
                       let w__38 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                       let w__39 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                       let w__40 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                       (pure (((((_get_HCR_EL2_Type_NV w__38) +++ ((_get_HCR_EL2_Type_NV1 w__39) +++ (_get_HCR_EL2_Type_NV2
                                 w__40))) == 0b100#3) : Bool)))) : Bool)
                  then (pure true)
                  else
                    (do
                      let w__41 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__42 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__43 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_NV w__41) +++ ((_get_HCR_EL2_Type_NV1 w__42) +++ (_get_HCR_EL2_Type_NV2
                                w__43))) == 0b111#3) : Bool)))))
              else (pure false) ) : SailM Bool )
            if (w__45 : Bool)
            then
              (let spsr : (BitVec 64) := (Sail.BitVec.updateSubrange spsr 3 2 0b10#2)
              (pure (spsr)))
            else
              (do
                let w__49 ← (( do
                  if ((← do
                       (HaveNVExt ())) : Bool)
                  then
                    (do
                      let w__47 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__48 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_NV w__47) +++ (_get_HCR_EL2_Type_NV1 w__48)) == 0b10#2) : Bool))))
                  else (pure false) ) : SailM Bool )
                let spsr : (BitVec 64) :=
                  if (w__49 : Bool)
                  then (Sail.BitVec.updateSubrange spsr 3 2 0b10#2)
                  else spsr
                (pure (spsr))))
        else (pure (spsr)) ) : SailM (BitVec 64) )
      let w__52 ← (( do
        if ((← do
             (HaveBTIExt ())) : Bool)
        then
          (do
            let w__51 ← (( do (UsingAArch32 ()) ) : SailM Bool )
            (pure (((! w__51) : Bool))))
        else (pure false) ) : SailM Bool )
      let spsr ← (( do
        if (w__52 : Bool)
        then
          (do
            let zero_btype ← (( do (undefined_bool_at (← occLabel 720) ()) ) : SailM Bool )
            let zero_btype ← (( do
              if (((BEq.beq except.exceptype Exception_SError) || ((BEq.beq except.exceptype
                       Exception_IRQ) || ((BEq.beq except.exceptype Exception_FIQ) || ((BEq.beq
                           except.exceptype Exception_SoftwareStep) || ((BEq.beq except.exceptype
                             Exception_PCAlignment) || ((BEq.beq except.exceptype
                               Exception_InstructionAbort) || ((BEq.beq except.exceptype
                                 Exception_Breakpoint) || ((BEq.beq except.exceptype
                                   Exception_VectorCatch) || ((BEq.beq except.exceptype
                                     Exception_SoftwareBreakpoint) || ((BEq.beq except.exceptype
                                       Exception_IllegalState) || (BEq.beq except.exceptype
                                       Exception_BranchTarget))))))))))) : Bool)
              then (pure (false))
              else
                (do
                  (ConstrainUnpredictableBool Unpredictable_ZEROBTYPE)) ) : SailM Bool )
            let spsr : (BitVec 64) :=
              if (zero_btype : Bool)
              then (Sail.BitVec.updateSubrange spsr 11 10 0b00#2)
              else spsr
            (pure (spsr)))
        else (pure (spsr)) ) : SailM (BitVec 64) )
      let w__56 ← (( do
        (pure ((← do
              (pure ((← do
                    (HaveNV2Ext ())) && ((BEq.beq except.exceptype Exception_NV2DataAbort) : Bool)))) && ((target_el == EL3) : Bool)))
        ) : SailM Bool )
      let except : ExceptionRecord :=
        if (w__56 : Bool)
        then { except with exceptype := Exception_DataAbort }
        else except
      if ((! ((BEq.beq except.exceptype Exception_IRQ) || (BEq.beq except.exceptype Exception_FIQ))) : Bool)
      then
        (do
          (AArch64_ReportException except target_el))
      else (pure (()))
      let w__57 ← (( do (HaveBRBExt ()) ) : SailM Bool )
      if (w__57 : Bool)
      then
        (do
          let w__58 ← (( do (VBAR_read target_el) ) : SailM (BitVec 64) )
          (BRBEException except preferred_exception_return
            ((Sail.BitVec.extractLsb w__58 63 11) +++ (integer_subrange vect_offset 10 0)) target_el
            except.trappedsyscallinst))
      else (pure (()))
      let w__59 ← (( do (HaveGCS ()) ) : SailM Bool )
      if (w__59 : Bool)
      then
        (do
          let w__60 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((w__60.EL == target_el) : Bool)
          then
            (do
              let w__61 ← (( do (GetCurrentEXLOCKEN ()) ) : SailM Bool )
              if (w__61 : Bool)
              then
                (do
                  let w__62 ← (( do readReg PSTATE ) : SailM ProcState )
                  writeReg PSTATE { w__62 with EXLOCK := 1#1 })
              else
                (do
                  let w__63 ← (( do readReg PSTATE ) : SailM ProcState )
                  writeReg PSTATE { w__63 with EXLOCK := 0#1 }))
          else
            (do
              let w__64 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__64 with EXLOCK := 0#1 }))
      else (pure (()))
      let w__65 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__65 with EL := target_el }
      let w__66 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__66 with nRW := 0#1 }
      let w__67 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__67 with SP := 1#1 }
      (SPSR_set (N := 64) spsr)
      (ELR_set__1 preferred_exception_return)
      let w__68 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__68 with SS := 0#1 }
      let w__71 ← (( do
        if ((← do
             (HaveFeatNMI ())) : Bool)
        then
          (do
            let w__70 ← (( do (ELUsingAArch32 target_el) ) : SailM Bool )
            (pure (((! w__70) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__71 : Bool)
      then
        (do
          let w__72 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__73 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
          writeReg PSTATE { w__72 with ALLINT := (Complement.complement
              (_get_SCTLRType_SPINTMASK w__73)) })
      else (pure (()))
      let w__74 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__74 with D := (Sail.BitVec.extractLsb 0b1111#4 3 3) }
      let w__75 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__75 with A := (Sail.BitVec.extractLsb 0b1111#4 2 2) }
      let w__76 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__76 with I := (Sail.BitVec.extractLsb 0b1111#4 1 1) }
      let w__77 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__77 with F := (Sail.BitVec.extractLsb 0b1111#4 0 0) }
      let w__78 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__78 with IL := 0#1 }
      if (from_32 : Bool)
      then
        (do
          let w__79 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__79 with IT := 0b00000000#8 }
          let w__80 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__80 with T := 0#1 })
      else (pure (()))
      let w__89 ← (( do
        if ((← do
             if ((← do
                  (HavePANExt ())) : Bool)
             then
               (do
                 if ((← do
                      let w__82 ← (( do readReg PSTATE ) : SailM ProcState )
                      (pure (((w__82.EL == EL1) : Bool)))) : Bool)
                 then (pure true)
                 else
                   (do
                     if ((← do
                          let w__83 ← (( do readReg PSTATE ) : SailM ProcState )
                          (pure (((w__83.EL == EL2) : Bool)))) : Bool)
                     then
                       (do
                         (ELIsInHost EL0))
                     else (pure false)))
             else (pure false)) : Bool)
        then
          (do
            let w__88 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
            (pure ((((_get_SCTLRType_SPAN w__88) == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__89 : Bool)
      then
        (do
          let w__90 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__90 with PAN := 1#1 })
      else (pure (()))
      let w__91 ← (( do (HaveUAOExt ()) ) : SailM Bool )
      if (w__91 : Bool)
      then
        (do
          let w__92 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__92 with UAO := 0#1 })
      else (pure (()))
      let w__93 ← (( do (HaveBTIExt ()) ) : SailM Bool )
      if (w__93 : Bool)
      then
        (do
          let w__94 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__94 with BTYPE := 0b00#2 }
          writeReg BTypeNext 0b00#2)
      else (pure (()))
      let w__95 ← (( do (HaveSSBSExt ()) ) : SailM Bool )
      if (w__95 : Bool)
      then
        (do
          let w__96 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__97 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
          writeReg PSTATE { w__96 with SSBS := (_get_SCTLRType_DSSBS w__97) })
      else (pure (()))
      let w__98 ← (( do (HaveMTEExt ()) ) : SailM Bool )
      if (w__98 : Bool)
      then
        (do
          let w__99 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__99 with TCO := 1#1 })
      else (pure (()))
      let branch_conditional : Bool := false
      let w__100 ← (( do (VBAR_read__1 ()) ) : SailM (BitVec 64) )
      (BranchTo ((Sail.BitVec.extractLsb w__100 63 11) +++ (integer_subrange vect_offset 10 0))
        BranchType_EXCEPTION branch_conditional)
      (CheckExceptionCatch true)
      if (sync_errors : Bool)
      then
        (do
          let _ : Unit := (SynchronizeErrors ())
          let iesb_req : Bool := true
          (TakeUnmaskedPhysicalSErrorInterrupts iesb_req))
      else (pure (()))
      (EndOfInstruction ()))


/-- Type quantifiers: vect_offset : Int -/
def AArch32_EnterHypMode (except : ExceptionRecord) (preferred_exception_return : (BitVec 32)) (vect_offset : Int) : SailM Unit := do
  let _ : Unit := (SynchronizeContext ())
  let w__4 ← (( do
    if ((← do
         if ((← do
              (HaveEL EL2)) : Bool)
         then
           (do
             let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
             (pure (((BEq.beq w__1 SS_NonSecure) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        (ELUsingAArch32 EL2))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:13955.87-13955.88"
  let w__5 ← (( do (Halted ()) ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      (AArch32_EnterHypModeInDebugState except))
  else
    (do
      let spsr ← (( do (GetPSRFromPSTATE AArch32_NonDebugState 32) ) : SailM (BitVec 32) )
      if ((! ((BEq.beq except.exceptype Exception_IRQ) || (BEq.beq except.exceptype Exception_FIQ))) : Bool)
      then
        (do
          (AArch32_ReportHypEntry except))
      else (pure (()))
      (AArch32_WriteMode M32_Hyp)
      (SPSR_set (N := 32) spsr)
      (ELR_hyp_write preferred_exception_return)
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__7 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
      writeReg PSTATE { w__6 with T := (_get_HSCTLR_Type_TE w__7) }
      let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__8 with SS := 0#1 }
      let w__11 ← (( do
        if ((← do
             let w__9 ← (( do (HaveEL EL3) ) : SailM Bool )
             (pure (((! w__9) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__10 ← (( do (SCR_GEN_read ()) ) : SailM (BitVec 64) )
            (pure ((((_get_SCRType_EA w__10) == 0#1) : Bool)))) ) : SailM Bool )
      if (w__11 : Bool)
      then
        (do
          let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__12 with A := 1#1 })
      else (pure (()))
      let w__15 ← (( do
        if ((← do
             let w__13 ← (( do (HaveEL EL3) ) : SailM Bool )
             (pure (((! w__13) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__14 ← (( do (SCR_GEN_read ()) ) : SailM (BitVec 64) )
            (pure ((((_get_SCRType_IRQ w__14) == 0#1) : Bool)))) ) : SailM Bool )
      if (w__15 : Bool)
      then
        (do
          let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__16 with I := 1#1 })
      else (pure (()))
      let w__19 ← (( do
        if ((← do
             let w__17 ← (( do (HaveEL EL3) ) : SailM Bool )
             (pure (((! w__17) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__18 ← (( do (SCR_GEN_read ()) ) : SailM (BitVec 64) )
            (pure ((((_get_SCRType_FIQ w__18) == 0#1) : Bool)))) ) : SailM Bool )
      if (w__19 : Bool)
      then
        (do
          let w__20 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__20 with F := 1#1 })
      else (pure (()))
      let w__21 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__22 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
      writeReg PSTATE { w__21 with E := (_get_HSCTLR_Type_EE w__22) }
      let w__23 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__23 with IL := 0#1 }
      let w__24 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__24 with IT := 0b00000000#8 }
      let w__25 ← (( do (HaveSSBSExt ()) ) : SailM Bool )
      if (w__25 : Bool)
      then
        (do
          let w__26 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__27 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
          writeReg PSTATE { w__26 with SSBS := (_get_HSCTLR_Type_DSSBS w__27) })
      else (pure (()))
      let branch_conditional : Bool := false
      let w__28 ← (( do (HVBAR_read ()) ) : SailM (BitVec 32) )
      (BranchTo ((Sail.BitVec.extractLsb w__28 31 5) +++ (integer_subrange vect_offset 4 0))
        BranchType_EXCEPTION branch_conditional)
      (CheckExceptionCatch true)
      (EndOfInstruction ()))


end ArmFull.Functions
