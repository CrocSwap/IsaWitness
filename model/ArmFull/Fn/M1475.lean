import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0016
import ArmFull.Fn.M0021
import ArmFull.Fn.M0024
import ArmFull.Fn.M0038
import ArmFull.Fn.M0043
import ArmFull.Fn.M0058
import ArmFull.Fn.M0087
import ArmFull.Fn.M0100
import ArmFull.Fn.M0118
import ArmFull.Fn.M0143
import ArmFull.Fn.M0153
import ArmFull.Fn.M0166
import ArmFull.Fn.M0212
import ArmFull.Fn.M0226
import ArmFull.Fn.M0242
import ArmFull.Fn.M0243
import ArmFull.Fn.M0246
import ArmFull.Fn.M0247
import ArmFull.Fn.M0253
import ArmFull.Fn.M0254
import ArmFull.Fn.M0260
import ArmFull.Fn.M0583
import ArmFull.Fn.M0851
import ArmFull.Fn.M1001
import ArmFull.Fn.M1072
import ArmFull.Fn.M1142
import ArmFull.Fn.M1467
import ArmFull.Fn.M1468
import ArmFull.Fn.M1474

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

/-- Type quantifiers: pc : Int -/
def __DecodeA64 (pc : Int) (opcode : (BitVec 32)) : SailM Unit := do
  let v__0 := opcode
  if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb v__0 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
           v__0 28 25)) == (0x0#4 : (BitVec 4)))) : Bool)
  then
    (do
      (__DecodeA64_Reserved pc opcode))
  else
    (do
      if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb v__0 31 31)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
               v__0 28 25)) == (0x0#4 : (BitVec 4)))) : Bool)
      then
        (do
          (__DecodeA64_SME pc opcode))
      else
        (do
          if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb v__0 28 25)) == (0x1#4 : (BitVec 4))) : Bool)
          then
            (do
              (__DecodeA64_Unallocated1 pc opcode))
          else
            (do
              if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb v__0 28 25)) == (0x2#4 : (BitVec 4))) : Bool)
              then
                (do
                  (__DecodeA64_SVE pc opcode))
              else
                (do
                  if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb v__0 28 25)) == (0x3#4 : (BitVec 4))) : Bool)
                  then
                    (do
                      (__DecodeA64_Unallocated2 pc opcode))
                  else
                    (do
                      if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb v__0 28 26)) == (0b100#3 : (BitVec 3))) : Bool)
                      then
                        (do
                          (__DecodeA64_DataProcImm pc opcode))
                      else
                        (do
                          if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb v__0 28 26)) == (0b101#3 : (BitVec 3))) : Bool)
                          then
                            (do
                              (__DecodeA64_BranchExcSys pc opcode))
                          else
                            (do
                              if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb v__0 27
                                       27)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       v__0 25 25)) == (0#1 : (BitVec 1)))) : Bool)
                              then
                                (do
                                  (__DecodeA64_LoadStore pc opcode))
                              else
                                (do
                                  if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb v__0
                                         27 25)) == (0b101#3 : (BitVec 3))) : Bool)
                                  then
                                    (do
                                      (__DecodeA64_DataProcReg pc opcode))
                                  else
                                    (do
                                      (__DecodeA64_DataProcFPSIMD pc opcode))))))))))


def ExecuteA64 (instr : (BitVec 32)) : SailM Unit := do
  let w__0 ← (( do (Halted ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      sailTryCatch ((do
          let w__1 ← (( do (__DefaultCond __A64) ) : SailM (BitVec 4) )
          (__SetThisInstrDetails __A64 instr w__1)
          let w__2 ← (( do readReg _PC ) : SailM (BitVec 64) )
          (__DecodeA64 (BitVec.toNat w__2) instr))) (fun the_exception => 
        match the_exception with
          | exn =>
            (do
              if ((IsExceptionTaken exn) : Bool)
              then (pure (()))
              else
                (do
                  if ((((IsSEE exn) || (IsUNDEFINED exn)) || (IsUNPREDICTABLE exn)) : Bool)
                  then
                    (do
                      (AArch64_UndefinedFault ()))
                  else sailThrow (exn)))))
  else
    (do
      let w__3 ← (( do readReg _PC ) : SailM (BitVec 64) )
      (__DecodeA64 (BitVec.toNat w__3) instr))


def __TryDecodeExecute (enc : __InstrEnc) (instr : (BitVec 32)) : SailM Unit := do
  match enc with
  | .__A64 =>
    (do
      (ExecuteA64 instr))
  | .__A32 =>
    (do
      (ExecuteA32 instr))
  | .__T16 =>
    (do
      (ExecuteT16 (Sail.BitVec.extractLsb instr 15 0)))
  | .__T32 =>
    (do
      (ExecuteT32__1 instr))


def __DecodeExecute (enc : __InstrEnc) (instr : (BitVec 32)) : SailM Unit := do
  sailTryCatch ((do
      (__TryDecodeExecute enc instr))) (fun the_exception => 
    match the_exception with
      | exn =>
        (do
          if ((IsSEE exn) : Bool)
          then
            (do
              (__TryDecodeExecute enc instr))
          else sailThrow (exn)))


def __InstructionExecute (_ : Unit) : SailM Unit := do
  let enc ← (( do (undefined___InstrEnc (.site 7637) ()) ) : SailM __InstrEnc )
  let instr ← (( do (undefined_bitvector_at (.site 7638) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  (EDSCR_write (_update_EDSCR_Type_PipeAdv w__0 1#1))
  let w__1 ← (( do readReg EDESR ) : SailM (BitVec 32) )
  if ((! (IsZero w__1)) : Bool)
  then
    (do
      (CheckPendingOSUnlockCatch ())
      (CheckPendingResetCatch ())
      (CheckPendingExceptionCatch true))
  else (pure (()))
  sailTryCatch ((do
      let w__4 ← (( do
        if ((← do
             let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__2.nRW == 1#1) : Bool)))) : Bool)
        then
          (do
            let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__3.T == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      writeReg ShouldAdvanceIT w__4
      writeReg ShouldAdvanceSS true
      let pc ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
      let w__5 ← (( do (__FetchInstr pc) ) : SailM (__InstrEnc × (BitVec 32)) )
      let (tup__0, tup__1) := (w__5 : (__InstrEnc × (BitVec 32)))
      let enc : __InstrEnc := tup__0
      let instr : (BitVec 32) := tup__1
      (__CheckForEmulatorTermination enc instr)
      (PMUEvent PMU_EVENT_INST_SPEC)
      writeReg __BranchTaken false
      writeReg __ExclusiveMonitorSet false
      let w__6 ← (( do (__DefaultCond enc) ) : SailM (BitVec 4) )
      (__SetThisInstrDetails enc instr w__6)
      (SPEPreExecution ())
      (__DecodeExecute enc instr)
      (PMUEvent PMU_EVENT_INST_RETIRED))) (fun the_exception => 
    match the_exception with
      | exn =>
        (do
          if ((((IsSEE exn) || (IsUNDEFINED exn)) || (IsUNPREDICTABLE exn)) : Bool)
          then
            (do
              let w__7 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              if (w__7 : Bool)
              then
                (do
                  match enc with
                  | .__A32 =>
                    (do
                      (UnallocatedA32_Instruction instr))
                  | .__T16 =>
                    (do
                      (UnallocatedT32_16_Instruction (Sail.BitVec.extractLsb instr 15 0)))
                  | .__T32 =>
                    (do
                      (UnallocatedT32_32_Instruction instr))
                  | _ =>
                    (do
                      (Unreachable ())))
              else
                (do
                  (AArch64_UndefinedFault ())))
          else
            (do
              if ((IsExceptionTaken exn) : Bool)
              then (pure (()))
              else sailThrow (exn))))
  (SPEPostExecution ())
  writeReg InGuardedPage false
  let w__8 ← (( do (AArch64_ExecutingERETInstr ()) ) : SailM Bool )
  if ((! w__8) : Bool)
  then
    (do
      let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__10 ← (( do readReg BTypeNext ) : SailM (BitVec 2) )
      writeReg PSTATE { w__9 with BTYPE := w__10 })
  else (pure (()))
  let w__11 ← (( do readReg __BranchTaken ) : SailM Bool )
  if ((! w__11) : Bool)
  then
    (do
      let w__12 ← (( do readReg _PC ) : SailM (BitVec 64) )
      let w__13 ← (( do (ThisInstrLength ()) ) : SailM Int )
      writeReg _PC (Sail.BitVec.extractLsb (BitVec.addInt w__12 (fdiv_int w__13 8)) 63 0))
  else (pure (()))
  let w__14 ← (( do readReg ShouldAdvanceIT ) : SailM Bool )
  if (w__14 : Bool)
  then
    (do
      (AArch32_ITAdvance ()))
  else (pure (()))
  let w__15 ← (( do readReg ShouldAdvanceSS ) : SailM Bool )
  if (w__15 : Bool)
  then
    (do
      (SSAdvance ()))
  else (pure (()))


def __TopLevel (_ : Unit) : SailM Unit := do
  let interrupt_taken ← (( do (undefined_bool_at (.site 7639) ()) ) : SailM Bool )
  let w__0 ← (( do (Halted ()) ) : SailM Bool )
  if (w__0 : Bool)
  then (pure (()))
  else
    (do
      let interrupt_req ← (( do (undefined_InterruptReq (.site 7640) ()) ) : SailM InterruptReq )
      let interrupt_req : InterruptReq := { interrupt_req with take_SE := true }
      let interrupt_req : InterruptReq := { interrupt_req with take_vSE := true }
      let interrupt_req : InterruptReq := { interrupt_req with take_IRQ := true }
      let interrupt_req : InterruptReq := { interrupt_req with take_vIRQ := true }
      let interrupt_req : InterruptReq := { interrupt_req with take_FIQ := true }
      let interrupt_req : InterruptReq := { interrupt_req with take_vFIQ := true }
      sailTryCatch ((do
          let interrupt_taken ← (( do (TakePendingInterrupts interrupt_req) ) : SailM Bool )
          if ((! interrupt_taken) : Bool)
          then
            (do
              let w__1 ← (( do readReg Branchtypetaken ) : SailM BranchType )
              if ((BEq.beq w__1 BranchType_RESET) : Bool)
              then
                (do
                  (CheckResetCatch ())
                  writeReg Branchtypetaken BranchType_UNKNOWN)
              else (pure (()))
              (__InstructionExecute ()))
          else (pure (())))) (fun the_exception => 
        match the_exception with
          | .Error_SError iesb_req =>
            (do
              let w__2 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              if (w__2 : Bool)
              then
                (do
                  (AArch32_TakePhysicalSErrorException iesb_req))
              else
                (do
                  (AArch64_TakePhysicalSErrorException iesb_req)))
          | .Error_ExceptionTaken () => (pure (()))
          | e => sailThrow (e)))


end ArmFull.Functions
