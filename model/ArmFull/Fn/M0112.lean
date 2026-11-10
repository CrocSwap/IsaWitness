import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0024
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043

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

def _set_CPACR_EL1_Type_SMEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CPACR_EL1_Type_SMEN r v)


def _set_CPTR_EL2_Type_SMEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CPTR_EL2_Type_SMEN r v)


def _set_CPACR_EL1_Type_TTA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CPACR_EL1_Type_TTA r v)


def _set_CPTR_EL3_Type_TTA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CPTR_EL3_Type_TTA r v)


def _set_HCPTR_Type_TTA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HCPTR_Type_TTA r v)


def _set_CPACR_EL1_Type_ZEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CPACR_EL1_Type_ZEN r v)


def _set_CPTR_EL2_Type_ZEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CPTR_EL2_Type_ZEN r v)


def _set_CPTR_EL2_Type_TAM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CPTR_EL2_Type_TAM r v)


def _set_CPTR_EL3_Type_TAM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CPTR_EL3_Type_TAM r v)


def _set_HCPTR_Type_TAM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HCPTR_Type_TAM r v)


def _set_CPTR_EL2_Type_TCPAC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CPTR_EL2_Type_TCPAC r v)


def _set_CPTR_EL3_Type_TCPAC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CPTR_EL3_Type_TCPAC r v)


def _set_HCPTR_Type_TCPAC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HCPTR_Type_TCPAC r v)


def _set_CPTR_EL2_Type_TFP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CPTR_EL2_Type_TFP r v)


def _set_CPTR_EL3_Type_TFP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CPTR_EL3_Type_TFP r v)


def _set_CPTR_EL2_Type_TSM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CPTR_EL2_Type_TSM r v)


def _set_CPTR_EL2_Type_TZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CPTR_EL2_Type_TZ r v)


def _set_CPTR_EL3_Type_ESM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CPTR_EL3_Type_ESM r v)


def _set_CPTR_EL3_Type_EZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CPTR_EL3_Type_EZ r v)


def _set_CPACR_Type_ASEDIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CPACR_Type_ASEDIS r v)


def _set_CPACR_Type_TRCDIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CPACR_Type_TRCDIS r v)


def _set_CPACR_Type_cp10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CPACR_Type_cp10 r v)


def _set_NSACR_Type_cp10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_NSACR_Type_cp10 r v)


def _set_CPACR_Type_cp11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CPACR_Type_cp11 r v)


def _set_NSACR_Type_cp11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_NSACR_Type_cp11 r v)


def _set_HCPTR_Type_TASE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HCPTR_Type_TASE r v)


def _set_HCPTR_Type_TCP10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HCPTR_Type_TCP10 r v)


def _set_HCPTR_Type_TCP11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HCPTR_Type_TCP11 r v)


def _set_NSACR_Type_NSASEDIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_NSACR_Type_NSASEDIS r v)


def _set_NSACR_Type_NSTRCDIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_NSACR_Type_NSTRCDIS r v)


def SP_set (value_name : (BitVec 64)) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.SP == 0#1) : Bool)
  then
    (do
      writeReg SP_EL0 value_name)
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let questionMark := w__1.EL
      if ((questionMark == EL0) : Bool)
      then
        (do
          writeReg SP_EL0 value_name)
      else
        (do
          if ((questionMark == EL1) : Bool)
          then
            (do
              writeReg SP_EL1 value_name)
          else
            (do
              if ((questionMark == EL2) : Bool)
              then
                (do
                  writeReg SP_EL2 value_name)
              else
                (do
                  if ((questionMark == EL3) : Bool)
                  then
                    (do
                      writeReg SP_EL3 value_name)
                  else (pure (()))))))


def _set_DBGOSDLR_Type_DLK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGOSDLR_Type_DLK r v)


def _set_EDPRSR_Type_DLK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDPRSR_Type_DLK r v)


def _set_OSDLR_EL1_Type_DLK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_OSDLR_EL1_Type_DLK r v)


def _set_DBGPRCR_EL1_Type_CORENPDRQ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGPRCR_EL1_Type_CORENPDRQ r v)


def _set_DBGPRCR_Type_CORENPDRQ (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGPRCR_Type_CORENPDRQ r v)


def _set_EDPRCR_Type_CORENPDRQ (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDPRCR_Type_CORENPDRQ r v)


def _set_GCSCR_EL1_Type_EXLOCKEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSCR_EL1_Type_EXLOCKEN r v)


def _set_GCSCR_EL2_Type_EXLOCKEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSCR_EL2_Type_EXLOCKEN r v)


def _set_GCSCR_EL3_Type_EXLOCKEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSCR_EL3_Type_EXLOCKEN r v)


def _set_GCSCR_EL1_Type_PCRSEL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSCR_EL1_Type_PCRSEL r v)


def _set_GCSCRE0_EL1_Type_PCRSEL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSCRE0_EL1_Type_PCRSEL r v)


def _set_GCSCR_EL2_Type_PCRSEL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSCR_EL2_Type_PCRSEL r v)


def _set_GCSCR_EL3_Type_PCRSEL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSCR_EL3_Type_PCRSEL r v)


def _set_GCSCR_EL1_Type_PUSHMEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSCR_EL1_Type_PUSHMEn r v)


def _set_GCSCRE0_EL1_Type_PUSHMEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSCRE0_EL1_Type_PUSHMEn r v)


def _set_GCSCR_EL2_Type_PUSHMEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSCR_EL2_Type_PUSHMEn r v)


def _set_GCSCR_EL3_Type_PUSHMEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSCR_EL3_Type_PUSHMEn r v)


def _set_GCSCR_EL1_Type_RVCHKEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSCR_EL1_Type_RVCHKEN r v)


def _set_GCSCRE0_EL1_Type_RVCHKEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSCRE0_EL1_Type_RVCHKEN r v)


def _set_GCSCR_EL2_Type_RVCHKEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSCR_EL2_Type_RVCHKEN r v)


def _set_GCSCR_EL3_Type_RVCHKEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSCR_EL3_Type_RVCHKEN r v)


def _set_GCSCR_EL1_Type_STREn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSCR_EL1_Type_STREn r v)


def _set_GCSCRE0_EL1_Type_STREn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSCRE0_EL1_Type_STREn r v)


def _set_GCSCR_EL2_Type_STREn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSCR_EL2_Type_STREn r v)


def _set_GCSCR_EL3_Type_STREn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSCR_EL3_Type_STREn r v)


def GetCurrentEXLOCKEN (_ : Unit) : SailM Bool := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let questionMark := w__0.EL
  if ((questionMark == EL0) : Bool)
  then
    (do
      (Unreachable ())
      (undefined_bool_at (← occLabel 638) ()))
  else
    (do
      if ((questionMark == EL1) : Bool)
      then
        (do
          let w__2 ← (( do readReg GCSCR_EL1 ) : SailM (BitVec 64) )
          (pure (((_get_GCSCR_EL1_Type_EXLOCKEN w__2) == 1#1))))
      else
        (do
          if ((questionMark == EL2) : Bool)
          then
            (do
              let w__3 ← (( do readReg GCSCR_EL2 ) : SailM (BitVec 64) )
              (pure (((_get_GCSCR_EL2_Type_EXLOCKEN w__3) == 1#1))))
          else
            (do
              if ((questionMark == EL3) : Bool)
              then
                (do
                  let w__4 ← (( do readReg GCSCR_EL3 ) : SailM (BitVec 64) )
                  (pure (((_get_GCSCR_EL3_Type_EXLOCKEN w__4) == 1#1))))
              else
                (do
                  (undefined_bool_at (← occLabel 637) ())))))


def _set_MDSCR_EL1_Type_EHBWE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDSCR_EL1_Type_EHBWE r v)


def _set_EDSCR2_Type_EHBWE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDSCR2_Type_EHBWE r v)


def _set_MDSCR_EL1_Type_EMBWE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDSCR_EL1_Type_EMBWE r v)


def _set_MDSCR_EL1_Type_KDE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDSCR_EL1_Type_KDE r v)


def _set_MDSCR_EL1_Type_MDE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDSCR_EL1_Type_MDE r v)


def _set_OSLSR_EL1_Type_OSLK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_OSLSR_EL1_Type_OSLK r v)


def _set_DBGOSLSR_Type_OSLK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGOSLSR_Type_OSLK r v)


def _set_EDPRSR_Type_OSLK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDPRSR_Type_OSLK r v)


def _set_OSLAR_EL1_Type_OSLK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_OSLAR_EL1_Type_OSLK r v)


def _set_OSLSR_EL1_Type_OSLM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_OSLSR_EL1_Type_OSLM r v)


def _set_DBGOSLSR_Type_OSLM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGOSLSR_Type_OSLM r v)


def _set_OSLSR_EL1_Type_nTT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_OSLSR_EL1_Type_nTT r v)


def _set_CTILSR_Type_nTT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTILSR_Type_nTT r v)


def _set_DBGOSLSR_Type_nTT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGOSLSR_Type_nTT r v)


def _set_EDLSR_Type_nTT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDLSR_Type_nTT r v)


def _set_PMLSR_Type_nTT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMLSR_Type_nTT r v)


def _set_HCR_Type_TAC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HCR_Type_TAC r v)


def _set_HCR_Type_VA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HCR_Type_VA r v)


def _set_DBGBVR_EL1_Type_VA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 55)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGBVR_EL1_Type_VA r v)


def _set_DBGBVR_Type_VA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 30)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGBVR_Type_VA r v)


def _set_DBGWVR_EL1_Type_VA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 55)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGWVR_EL1_Type_VA r v)


def _set_DBGWVR_Type_VA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 30)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGWVR_Type_VA r v)


def Restarting (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  (pure (((_get_EDSCR_Type_STATUS w__0) == 0b000001#6)))


def _set_HSCTLR_Type_LSMAOE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HSCTLR_Type_LSMAOE r v)


def _set_SCTLR_EL1_Type_LSMAOE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL1_Type_LSMAOE r v)


def _set_SCTLR_EL2_Type_LSMAOE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL2_Type_LSMAOE r v)


def _set_SCTLR_Type_LSMAOE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SCTLR_Type_LSMAOE r v)


def _set_HSCTLR_Type_nTLSMD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HSCTLR_Type_nTLSMD r v)


def _set_SCTLR_EL1_Type_nTLSMD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL1_Type_nTLSMD r v)


def _set_SCTLR_EL2_Type_nTLSMD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL2_Type_nTLSMD r v)


def _set_SCTLR_Type_nTLSMD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SCTLR_Type_nTLSMD r v)


def _set_SCTLR_EL2_Type_ATA0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL2_Type_ATA0 r v)


def _set_SCTLR_EL1_Type_ATA0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL1_Type_ATA0 r v)


def _set_SCTLR_EL2_Type_BT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL2_Type_BT r v)


def _set_DBGBCR_EL1_Type_BT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGBCR_EL1_Type_BT r v)


def _set_DBGBCR_Type_BT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGBCR_Type_BT r v)


def _set_ID_AA64PFR1_EL1_Type_BT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_BT r v)


def _set_SCTLR_EL3_Type_BT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL3_Type_BT r v)


def _set_SCTLR_EL2_Type_BT0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL2_Type_BT0 r v)


def _set_SCTLR_EL1_Type_BT0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL1_Type_BT0 r v)


def _set_SCTLR_EL2_Type_CMOW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL2_Type_CMOW r v)


def _set_HCRX_EL2_Type_CMOW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCRX_EL2_Type_CMOW r v)


def _set_ID_AA64MMFR1_EL1_Type_CMOW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_CMOW r v)


def _set_SCTLR_EL1_Type_CMOW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL1_Type_CMOW r v)


def _set_SCTLR_EL2_Type_EIS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL2_Type_EIS r v)


def _set_SCTLR_EL1_Type_EIS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL1_Type_EIS r v)


def _set_SCTLR_EL3_Type_EIS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL3_Type_EIS r v)


def _set_SCTLR_EL2_Type_EOS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL2_Type_EOS r v)


def _set_SCTLR_EL1_Type_EOS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL1_Type_EOS r v)


def _set_SCTLR_EL3_Type_EOS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL3_Type_EOS r v)


def _set_SCTLR_EL2_Type_EnALS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL2_Type_EnALS r v)


def _set_HCRX_EL2_Type_EnALS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCRX_EL2_Type_EnALS r v)


def _set_SCTLR_EL1_Type_EnALS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL1_Type_EnALS r v)


def _set_SCTLR_EL2_Type_EnASR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL2_Type_EnASR r v)


def _set_HCRX_EL2_Type_EnASR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCRX_EL2_Type_EnASR r v)


def _set_SCTLR_EL1_Type_EnASR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL1_Type_EnASR r v)


def _set_SCTLR_EL2_Type_EnDA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL2_Type_EnDA r v)


def _set_SCTLR_EL1_Type_EnDA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL1_Type_EnDA r v)


def _set_SCTLR_EL3_Type_EnDA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL3_Type_EnDA r v)


def _set_SCTLR_EL2_Type_EnDB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL2_Type_EnDB r v)


def _set_SCTLR_EL1_Type_EnDB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL1_Type_EnDB r v)


def _set_SCTLR_EL3_Type_EnDB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL3_Type_EnDB r v)


def _set_SCTLR_EL2_Type_EnIA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL2_Type_EnIA r v)


def _set_SCTLR_EL1_Type_EnIA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL1_Type_EnIA r v)


def _set_SCTLR_EL3_Type_EnIA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL3_Type_EnIA r v)


def _set_SCTLR_EL2_Type_EnIB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL2_Type_EnIB r v)


def _set_SCTLR_EL1_Type_EnIB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL1_Type_EnIB r v)


def _set_SCTLR_EL3_Type_EnIB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL3_Type_EnIB r v)


def _set_SCTLR_EL2_Type_EnRCTX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL2_Type_EnRCTX r v)


def _set_SCTLR_EL1_Type_EnRCTX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL1_Type_EnRCTX r v)


def _set_SCTLR_Type_EnRCTX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SCTLR_Type_EnRCTX r v)


def _set_SCTLR_EL2_Type_ITFSB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL2_Type_ITFSB r v)


def _set_SCTLR_EL1_Type_ITFSB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL1_Type_ITFSB r v)


def _set_SCTLR_EL3_Type_ITFSB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL3_Type_ITFSB r v)


def _set_SCTLR_EL2_Type_MSCEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL2_Type_MSCEn r v)


def _set_HCRX_EL2_Type_MSCEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCRX_EL2_Type_MSCEn r v)


def _set_SCTLR_EL1_Type_MSCEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL1_Type_MSCEn r v)


def _set_SCTLR_EL2_Type_TCF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL2_Type_TCF r v)


def _set_SCTLR_EL1_Type_TCF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL1_Type_TCF r v)


end ArmFull.Functions
