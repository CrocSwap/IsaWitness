import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0020
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0035
import ArmFull.Fn.M0043
import ArmFull.Fn.M0046
import ArmFull.Fn.M0049
import ArmFull.Fn.M0100
import ArmFull.Fn.M0112
import ArmFull.Fn.M0113
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0152
import ArmFull.Fn.M0153
import ArmFull.Fn.M0166
import ArmFull.Fn.M0172
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
import ArmFull.Fn.M0186
import ArmFull.Fn.M0196
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203
import ArmFull.Fn.M0216
import ArmFull.Fn.M0227
import ArmFull.Fn.M0237
import ArmFull.Fn.M0241
import ArmFull.Fn.M0244
import ArmFull.Fn.M0245
import ArmFull.Fn.M0246
import ArmFull.Fn.M0247

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

def decode_aarch32_instrs_HLT_A1enc_A_txt (cond : (BitVec 4)) (imm12 : (BitVec 12)) (imm4 : (BitVec 4)) : SailM Unit := do
  ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:42755.25-42755.26"
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


def decode_hlt_aarch64_instrs_system_exceptions_debug_halt (imm16 : (BitVec 16)) : SailM Unit := do
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
  let w__3 ← (( do (HaveBTIExt ()) ) : SailM Bool )
  if (w__3 : Bool)
  then
    (do
      (SetBTypeCompatible true))
  else (pure (()))
  (execute_aarch64_instrs_system_exceptions_debug_halt ())


/-- Type quantifiers: vect_offset_in : Int -/
def AArch64_TakeException (target_el : (BitVec 2)) (exception_in : ExceptionRecord) (preferred_exception_return : (BitVec 64)) (vect_offset_in : Int) : SailM Unit := do
  let w__3 ← (( do
    if ((← do
         if (((HaveEL target_el) : Bool) : Bool)
         then
           (do
             let w__0 ← (( do (ELUsingAArch32 target_el) ) : SailM Bool )
             (pure (((! w__0) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure ((((BitVec.toNat target_el) ≥b (BitVec.toNat w__2.EL)) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__3 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:10356.105-10356.106"
  let w__4 ← (( do (Halted ()) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      (AArch64_TakeExceptionInDebugState target_el exception_in))
  else
    (do
      let except : ExceptionRecord := exception_in
      let sync_errors ← (( do (undefined_bool_at (← occLabel 716) ()) ) : SailM Bool )
      let iesb_req ← (( do (undefined_bool_at (← occLabel 717) ()) ) : SailM Bool )
      let w__5 ← (( do (HaveIESB ()) ) : SailM Bool )
      let (iesb_req, sync_errors) ← (( do
        if (w__5 : Bool)
        then
          (do
            let w__6 ← (( do (SCTLR_read target_el) ) : SailM (BitVec 64) )
            let sync_errors := (((_get_SCTLRType_IESB w__6) == 1#1) : Bool)
            let w__7 ← (( do (HaveDoubleFaultExt ()) ) : SailM Bool )
            let sync_errors ← (( do
              if (w__7 : Bool)
              then
                (do
                  if ((sync_errors : Bool) : Bool)
                  then (pure true)
                  else
                    (do
                      (pure ((← do
                            let w__8 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                            let w__9 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                            (pure (((((_get_SCR_EL3_Type_EA w__8) +++ (_get_SCR_EL3_Type_NMEA w__9)) == 0b11#2) : Bool)))) && ((target_el == EL3) : Bool)))))
              else (pure (sync_errors)) ) : SailM Bool )
            let w__13 ← (( do
              if ((sync_errors : Bool) : Bool)
              then
                (do
                  (InsertIESBBeforeException target_el))
              else (pure false) ) : SailM Bool )
            if (w__13 : Bool)
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
      let w__16 ← (( do
        if ((← do
             (HaveTME ())) : Bool)
        then
          (do
            let w__15 ← (( do readReg TSTATE ) : SailM TMState )
            (pure (((w__15.depth >b 0) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__16 : Bool)
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
      let w__20 ← (( do
        if ((← if (from_32 : Bool)
             then
               (do
                 (HaveSME ()))
             else (pure false)) : Bool)
        then
          (do
            let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__19.SM == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__20 : Bool)
      then
        (do
          (ResetSVEState ()))
      else
        (do
          (MaybeZeroSVEUppers target_el))
      let vect_offset : Int := vect_offset_in
      let w__21 ← (( do readReg PSTATE ) : SailM ProcState )
      let vect_offset ← (( do
        if (((BitVec.toNat target_el) >b (BitVec.toNat w__21.EL)) : Bool)
        then
          (do
            let lower_32 ← (( do (undefined_bool_at (← occLabel 719) ()) ) : SailM Bool )
            let lower_32 ← (( do
              if ((target_el == EL3) : Bool)
              then
                (do
                  let w__22 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if (w__22 : Bool)
                  then
                    (do
                      (ELUsingAArch32 EL2))
                  else
                    (do
                      (ELUsingAArch32 EL1)))
              else
                (do
                  let w__28 ← (( do
                    (pure ((← do
                          if ((← do
                               (IsInHost ())) : Bool)
                          then
                            (do
                              let w__26 ← (( do readReg PSTATE ) : SailM ProcState )
                              (pure (((w__26.EL == EL0) : Bool))))
                          else (pure false)) && ((target_el == EL2) : Bool))) ) : SailM Bool )
                  if (w__28 : Bool)
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
            let w__31 ← (( do readReg PSTATE ) : SailM ProcState )
            let vect_offset : Int :=
              if ((w__31.SP == 1#1) : Bool)
              then (vect_offset +i (BitVec.toNat 0x200#12))
              else vect_offset
            (pure (vect_offset))) ) : SailM Int )
      let vect_offset : Int := vect_offset
      let spsr ← (( do (GetPSRFromPSTATE AArch64_NonDebugState 64) ) : SailM (BitVec 64) )
      let w__35 ← (( do
        if ((← do
             (pure ((← do
                   let w__32 ← (( do readReg PSTATE ) : SailM ProcState )
                   (pure (((w__32.EL == EL1) : Bool)))) && ((target_el == EL1) : Bool)))) : Bool)
        then
          (do
            (EL2Enabled ()))
        else (pure false) ) : SailM Bool )
      let spsr ← (( do
        if (w__35 : Bool)
        then
          (do
            let w__44 ← (( do
              if ((← do
                   (HaveNV2Ext ())) : Bool)
              then
                (do
                  if ((← do
                       let w__37 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                       let w__38 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                       let w__39 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                       (pure (((((_get_HCR_EL2_Type_NV w__37) +++ ((_get_HCR_EL2_Type_NV1 w__38) +++ (_get_HCR_EL2_Type_NV2
                                 w__39))) == 0b100#3) : Bool)))) : Bool)
                  then (pure true)
                  else
                    (do
                      let w__40 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__41 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__42 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_NV w__40) +++ ((_get_HCR_EL2_Type_NV1 w__41) +++ (_get_HCR_EL2_Type_NV2
                                w__42))) == 0b111#3) : Bool)))))
              else (pure false) ) : SailM Bool )
            if (w__44 : Bool)
            then
              (let spsr : (BitVec 64) := (Sail.BitVec.updateSubrange spsr 3 2 0b10#2)
              (pure (spsr)))
            else
              (do
                let w__48 ← (( do
                  if ((← do
                       (HaveNVExt ())) : Bool)
                  then
                    (do
                      let w__46 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__47 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_NV w__46) +++ (_get_HCR_EL2_Type_NV1 w__47)) == 0b10#2) : Bool))))
                  else (pure false) ) : SailM Bool )
                let spsr : (BitVec 64) :=
                  if (w__48 : Bool)
                  then (Sail.BitVec.updateSubrange spsr 3 2 0b10#2)
                  else spsr
                (pure (spsr))))
        else (pure (spsr)) ) : SailM (BitVec 64) )
      let w__51 ← (( do
        if ((← do
             (HaveBTIExt ())) : Bool)
        then
          (do
            let w__50 ← (( do (UsingAArch32 ()) ) : SailM Bool )
            (pure (((! w__50) : Bool))))
        else (pure false) ) : SailM Bool )
      let spsr ← (( do
        if (w__51 : Bool)
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
      let w__55 ← (( do
        (pure ((← do
              (pure ((← do
                    (HaveNV2Ext ())) && ((BEq.beq except.exceptype Exception_NV2DataAbort) : Bool)))) && ((target_el == EL3) : Bool)))
        ) : SailM Bool )
      let except : ExceptionRecord :=
        if (w__55 : Bool)
        then { except with exceptype := Exception_DataAbort }
        else except
      if ((! ((BEq.beq except.exceptype Exception_IRQ) || (BEq.beq except.exceptype Exception_FIQ))) : Bool)
      then
        (do
          (AArch64_ReportException except target_el))
      else (pure (()))
      let w__56 ← (( do (HaveBRBExt ()) ) : SailM Bool )
      if (w__56 : Bool)
      then
        (do
          let w__57 ← (( do (VBAR_read target_el) ) : SailM (BitVec 64) )
          (BRBEException except preferred_exception_return
            ((Sail.BitVec.extractLsb w__57 63 11) +++ (integer_subrange vect_offset 10 0)) target_el
            except.trappedsyscallinst))
      else (pure (()))
      let w__58 ← (( do (HaveGCS ()) ) : SailM Bool )
      if (w__58 : Bool)
      then
        (do
          let w__59 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((w__59.EL == target_el) : Bool)
          then
            (do
              let w__60 ← (( do (GetCurrentEXLOCKEN ()) ) : SailM Bool )
              if (w__60 : Bool)
              then
                (do
                  let w__61 ← (( do readReg PSTATE ) : SailM ProcState )
                  writeReg PSTATE { w__61 with EXLOCK := 1#1 })
              else
                (do
                  let w__62 ← (( do readReg PSTATE ) : SailM ProcState )
                  writeReg PSTATE { w__62 with EXLOCK := 0#1 }))
          else
            (do
              let w__63 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__63 with EXLOCK := 0#1 }))
      else (pure (()))
      let w__64 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__64 with EL := target_el }
      let w__65 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__65 with nRW := 0#1 }
      let w__66 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__66 with SP := 1#1 }
      (SPSR_set (N := 64) spsr)
      (ELR_set__1 preferred_exception_return)
      let w__67 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__67 with SS := 0#1 }
      let w__70 ← (( do
        if ((← do
             (HaveFeatNMI ())) : Bool)
        then
          (do
            let w__69 ← (( do (ELUsingAArch32 target_el) ) : SailM Bool )
            (pure (((! w__69) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__70 : Bool)
      then
        (do
          let w__71 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__72 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
          writeReg PSTATE { w__71 with ALLINT := (Complement.complement
              (_get_SCTLRType_SPINTMASK w__72)) })
      else (pure (()))
      let w__73 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__73 with D := (Sail.BitVec.extractLsb 0b1111#4 3 3) }
      let w__74 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__74 with A := (Sail.BitVec.extractLsb 0b1111#4 2 2) }
      let w__75 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__75 with I := (Sail.BitVec.extractLsb 0b1111#4 1 1) }
      let w__76 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__76 with F := (Sail.BitVec.extractLsb 0b1111#4 0 0) }
      let w__77 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__77 with IL := 0#1 }
      if (from_32 : Bool)
      then
        (do
          let w__78 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__78 with IT := 0b00000000#8 }
          let w__79 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__79 with T := 0#1 })
      else (pure (()))
      let w__88 ← (( do
        if ((← do
             if ((← do
                  (HavePANExt ())) : Bool)
             then
               (do
                 if ((← do
                      let w__81 ← (( do readReg PSTATE ) : SailM ProcState )
                      (pure (((w__81.EL == EL1) : Bool)))) : Bool)
                 then (pure true)
                 else
                   (do
                     if ((← do
                          let w__82 ← (( do readReg PSTATE ) : SailM ProcState )
                          (pure (((w__82.EL == EL2) : Bool)))) : Bool)
                     then
                       (do
                         (ELIsInHost EL0))
                     else (pure false)))
             else (pure false)) : Bool)
        then
          (do
            let w__87 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
            (pure ((((_get_SCTLRType_SPAN w__87) == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__88 : Bool)
      then
        (do
          let w__89 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__89 with PAN := 1#1 })
      else (pure (()))
      let w__90 ← (( do (HaveUAOExt ()) ) : SailM Bool )
      if (w__90 : Bool)
      then
        (do
          let w__91 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__91 with UAO := 0#1 })
      else (pure (()))
      let w__92 ← (( do (HaveBTIExt ()) ) : SailM Bool )
      if (w__92 : Bool)
      then
        (do
          let w__93 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__93 with BTYPE := 0b00#2 })
      else (pure (()))
      let w__94 ← (( do (HaveSSBSExt ()) ) : SailM Bool )
      if (w__94 : Bool)
      then
        (do
          let w__95 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__96 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
          writeReg PSTATE { w__95 with SSBS := (_get_SCTLRType_DSSBS w__96) })
      else (pure (()))
      let w__97 ← (( do (HaveMTEExt ()) ) : SailM Bool )
      if (w__97 : Bool)
      then
        (do
          let w__98 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__98 with TCO := 1#1 })
      else (pure (()))
      let branch_conditional : Bool := false
      let w__99 ← (( do (VBAR_read__1 ()) ) : SailM (BitVec 64) )
      (BranchTo ((Sail.BitVec.extractLsb w__99 63 11) +++ (integer_subrange vect_offset 10 0))
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
  let w__3 ← (( do
    if ((← do
         if (((HaveEL EL2) : Bool) : Bool)
         then
           (do
             let w__0 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
             (pure (((BEq.beq w__0 SS_NonSecure) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        (ELUsingAArch32 EL2))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__3 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:13942.87-13942.88"
  let w__4 ← (( do (Halted ()) ) : SailM Bool )
  if (w__4 : Bool)
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
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__6 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
      writeReg PSTATE { w__5 with T := (_get_HSCTLR_Type_TE w__6) }
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__7 with SS := 0#1 }
      let w__9 ← (( do
        if (((! (HaveEL EL3)) : Bool) : Bool)
        then (pure true)
        else
          (do
            let w__8 ← (( do (SCR_GEN_read ()) ) : SailM (BitVec 64) )
            (pure ((((_get_SCRType_EA w__8) == 0#1) : Bool)))) ) : SailM Bool )
      if (w__9 : Bool)
      then
        (do
          let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__10 with A := 1#1 })
      else (pure (()))
      let w__12 ← (( do
        if (((! (HaveEL EL3)) : Bool) : Bool)
        then (pure true)
        else
          (do
            let w__11 ← (( do (SCR_GEN_read ()) ) : SailM (BitVec 64) )
            (pure ((((_get_SCRType_IRQ w__11) == 0#1) : Bool)))) ) : SailM Bool )
      if (w__12 : Bool)
      then
        (do
          let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__13 with I := 1#1 })
      else (pure (()))
      let w__15 ← (( do
        if (((! (HaveEL EL3)) : Bool) : Bool)
        then (pure true)
        else
          (do
            let w__14 ← (( do (SCR_GEN_read ()) ) : SailM (BitVec 64) )
            (pure ((((_get_SCRType_FIQ w__14) == 0#1) : Bool)))) ) : SailM Bool )
      if (w__15 : Bool)
      then
        (do
          let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__16 with F := 1#1 })
      else (pure (()))
      let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__18 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
      writeReg PSTATE { w__17 with E := (_get_HSCTLR_Type_EE w__18) }
      let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__19 with IL := 0#1 }
      let w__20 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__20 with IT := 0b00000000#8 }
      let w__21 ← (( do (HaveSSBSExt ()) ) : SailM Bool )
      if (w__21 : Bool)
      then
        (do
          let w__22 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__23 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
          writeReg PSTATE { w__22 with SSBS := (_get_HSCTLR_Type_DSSBS w__23) })
      else (pure (()))
      let branch_conditional : Bool := false
      let w__24 ← (( do (HVBAR_read ()) ) : SailM (BitVec 32) )
      (BranchTo ((Sail.BitVec.extractLsb w__24 31 5) +++ (integer_subrange vect_offset 4 0))
        BranchType_EXCEPTION branch_conditional)
      (CheckExceptionCatch true)
      (EndOfInstruction ()))


/-- Type quantifiers: lr_offset : Int, vect_offset : Int -/
def AArch32_EnterMode (target_mode : (BitVec 5)) (preferred_exception_return : (BitVec 32)) (lr_offset : Int) (vect_offset : Int) : SailM Unit := do
  let _ : Unit := (SynchronizeContext ())
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL1)) : Bool)
    then
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__1.EL != EL2) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__2 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:14054.49-14054.50"
  let w__3 ← (( do (Halted ()) ) : SailM Bool )
  if (w__3 : Bool)
  then
    (do
      (AArch32_EnterModeInDebugState target_mode))
  else
    (do
      let spsr ← (( do (GetPSRFromPSTATE AArch32_NonDebugState 32) ) : SailM (BitVec 32) )
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__4.M == M32_Monitor) : Bool)
      then
        (do
          let w__5 ← (( do readReg SCR ) : SailM (BitVec 32) )
          writeReg SCR (Sail.BitVec.updateSubrange w__5 0 0 0#1))
      else (pure (()))
      (AArch32_WriteMode target_mode)
      (SPSR_set (N := 32) spsr)
      (R_set 14 (BitVec.addInt preferred_exception_return lr_offset))
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__7 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
      writeReg PSTATE { w__6 with T := (_get_SCTLR_Type_TE w__7) }
      let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__8 with SS := 0#1 }
      if ((target_mode == M32_FIQ) : Bool)
      then
        (do
          let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__9 with A := (Sail.BitVec.extractLsb 0b111#3 2 2) }
          let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__10 with I := (Sail.BitVec.extractLsb 0b111#3 1 1) }
          let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__11 with F := (Sail.BitVec.extractLsb 0b111#3 0 0) })
      else
        (do
          if (((target_mode == M32_Abort) || (target_mode == M32_IRQ)) : Bool)
          then
            (do
              let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__12 with A := (Sail.BitVec.extractLsb 0b11#2 1 1) }
              let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__13 with I := (Sail.BitVec.extractLsb 0b11#2 0 0) })
          else
            (do
              let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__14 with I := 1#1 }))
      let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__16 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
      writeReg PSTATE { w__15 with E := (_get_SCTLR_Type_EE w__16) }
      let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__17 with IL := 0#1 }
      let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__18 with IT := 0b00000000#8 }
      let w__21 ← (( do
        if ((← do
             (HavePANExt ())) : Bool)
        then
          (do
            let w__20 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
            (pure ((((_get_SCTLR_Type_SPAN w__20) == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__21 : Bool)
      then
        (do
          let w__22 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__22 with PAN := 1#1 })
      else (pure (()))
      let w__23 ← (( do (HaveSSBSExt ()) ) : SailM Bool )
      if (w__23 : Bool)
      then
        (do
          let w__24 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__25 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
          writeReg PSTATE { w__24 with SSBS := (_get_SCTLR_Type_DSSBS w__25) })
      else (pure (()))
      let branch_conditional : Bool := false
      let w__26 ← (( do (ExcVectorBase ()) ) : SailM (BitVec 32) )
      (BranchTo ((Sail.BitVec.extractLsb w__26 31 5) +++ (integer_subrange vect_offset 4 0))
        BranchType_EXCEPTION branch_conditional)
      (CheckExceptionCatch true)
      (EndOfInstruction ()))


end ArmFull.Functions
