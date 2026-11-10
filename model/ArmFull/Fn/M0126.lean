import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0056
import ArmFull.Fn.M0057
import ArmFull.Fn.M0058
import ArmFull.Fn.M0065
import ArmFull.Fn.M0066

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

def _set_ICC_IAR1_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_IAR1_EL1_Type_INTID r v)


def _set_ICC_IAR1_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICC_IAR1_Type_INTID r v)


def _set_ICC_NMIAR1_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_NMIAR1_EL1_Type_INTID r v)


def _set_ICC_SGI0R_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI0R_EL1_Type_INTID r v)


def _set_ICC_SGI0R_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI0R_Type_INTID r v)


def _set_ICC_SGI1R_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI1R_EL1_Type_INTID r v)


def _set_ICC_SGI1R_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI1R_Type_INTID r v)


def _set_ICV_DIR_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICV_DIR_EL1_Type_INTID r v)


def _set_ICV_DIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICV_DIR_Type_INTID r v)


def _set_ICV_EOIR0_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICV_EOIR0_EL1_Type_INTID r v)


def _set_ICV_EOIR0_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICV_EOIR0_Type_INTID r v)


def _set_ICV_EOIR1_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICV_EOIR1_EL1_Type_INTID r v)


def _set_ICV_EOIR1_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICV_EOIR1_Type_INTID r v)


def _set_ICV_HPPIR0_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICV_HPPIR0_EL1_Type_INTID r v)


def _set_ICV_HPPIR0_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICV_HPPIR0_Type_INTID r v)


def _set_ICV_HPPIR1_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICV_HPPIR1_EL1_Type_INTID r v)


def _set_ICV_HPPIR1_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICV_HPPIR1_Type_INTID r v)


def _set_ICV_IAR0_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICV_IAR0_EL1_Type_INTID r v)


def _set_ICV_IAR0_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICV_IAR0_Type_INTID r v)


def _set_ICV_IAR1_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICV_IAR1_EL1_Type_INTID r v)


def _set_ICV_IAR1_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICV_IAR1_Type_INTID r v)


def _set_ICH_LR_EL2_Type_Group (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_LR_EL2_Type_Group r v)


def _set_ICH_LRC_Type_Group (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_LRC_Type_Group r v)


def _set_ICH_LR_EL2_Type_HW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_LR_EL2_Type_HW r v)


def _set_ICH_LRC_Type_HW (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_LRC_Type_HW r v)


def _set_ICH_LR_EL2_Type_State (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_LR_EL2_Type_State r v)


def _set_ICH_LRC_Type_State (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_LRC_Type_State r v)


def _set_ICH_LR_EL2_Type_pINTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 13)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_LR_EL2_Type_pINTID r v)


def _set_GICR_CLRLPIR_Type_pINTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_CLRLPIR_Type_pINTID r v)


def _set_GICR_SETLPIR_Type_pINTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_SETLPIR_Type_pINTID r v)


def _set_ICH_LRC_Type_pINTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 13)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_LRC_Type_pINTID r v)


def _set_ICH_LR_EL2_Type_vINTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_LR_EL2_Type_vINTID r v)


def _set_GITS_SGIR_Type_vINTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_SGIR_Type_vINTID r v)


def _set_ICH_LR_Type_vINTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_LR_Type_vINTID r v)


def _set_MVFR0_EL1_Type_FPDP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MVFR0_EL1_Type_FPDP r v)


def _set_MVFR0_Type_FPDP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MVFR0_Type_FPDP r v)


def _set_MVFR0_EL1_Type_FPDivide (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MVFR0_EL1_Type_FPDivide r v)


def _set_MVFR0_Type_FPDivide (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MVFR0_Type_FPDivide r v)


def _set_MVFR0_EL1_Type_FPRound (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MVFR0_EL1_Type_FPRound r v)


def _set_MVFR0_Type_FPRound (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MVFR0_Type_FPRound r v)


def _set_MVFR0_EL1_Type_FPSP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MVFR0_EL1_Type_FPSP r v)


def _set_MVFR0_Type_FPSP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MVFR0_Type_FPSP r v)


def _set_MVFR0_EL1_Type_FPShVec (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MVFR0_EL1_Type_FPShVec r v)


def _set_MVFR0_Type_FPShVec (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MVFR0_Type_FPShVec r v)


def _set_MVFR0_EL1_Type_FPSqrt (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MVFR0_EL1_Type_FPSqrt r v)


def _set_MVFR0_Type_FPSqrt (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MVFR0_Type_FPSqrt r v)


def _set_MVFR0_EL1_Type_FPTrap (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MVFR0_EL1_Type_FPTrap r v)


def _set_MVFR0_Type_FPTrap (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MVFR0_Type_FPTrap r v)


def _set_MVFR0_EL1_Type_SIMDReg (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MVFR0_EL1_Type_SIMDReg r v)


def _set_MVFR0_Type_SIMDReg (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MVFR0_Type_SIMDReg r v)


def _set_ID_AA64DFR0_EL1_Type_BRBE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_BRBE r v)


def _set_ID_AA64DFR0_EL1_Type_BRPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_BRPs r v)


def _set_DBGDIDR_Type_BRPs (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDIDR_Type_BRPs r v)


def _set_EDDFR1_Type_BRPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDDFR1_Type_BRPs r v)


def _set_EDDFR_Type_BRPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDDFR_Type_BRPs r v)


def _set_ID_AA64DFR1_EL1_Type_BRPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR1_EL1_Type_BRPs r v)


def _set_ID_AA64DFR0_EL1_Type_CTX_CMPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_CTX_CMPs r v)


def _set_DBGDIDR_Type_CTX_CMPs (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDIDR_Type_CTX_CMPs r v)


def _set_EDDFR1_Type_CTX_CMPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDDFR1_Type_CTX_CMPs r v)


def _set_EDDFR_Type_CTX_CMPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDDFR_Type_CTX_CMPs r v)


def _set_ID_AA64DFR1_EL1_Type_CTX_CMPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR1_EL1_Type_CTX_CMPs r v)


def _set_ID_AA64DFR0_EL1_Type_DebugVer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_DebugVer r v)


def _set_ID_AA64DFR0_EL1_Type_DoubleLock (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_DoubleLock r v)


def _set_DBGDEVID_Type_DoubleLock (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDEVID_Type_DoubleLock r v)


def _set_ID_AA64DFR0_EL1_Type_ExtTrcBuff (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_ExtTrcBuff r v)


def _set_EDDFR_Type_ExtTrcBuff (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDDFR_Type_ExtTrcBuff r v)


def _set_ID_AA64DFR0_EL1_Type_HPMN0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_HPMN0 r v)


def _set_ID_DFR1_EL1_Type_HPMN0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_DFR1_EL1_Type_HPMN0 r v)


def _set_ID_DFR1_Type_HPMN0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_DFR1_Type_HPMN0 r v)


def _set_ID_AA64DFR0_EL1_Type_MTPMU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_MTPMU r v)


def _set_ID_DFR1_EL1_Type_MTPMU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_DFR1_EL1_Type_MTPMU r v)


def _set_ID_DFR1_Type_MTPMU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_DFR1_Type_MTPMU r v)


def _set_ID_AA64DFR0_EL1_Type_PMSS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_PMSS r v)


def _set_EDDFR_Type_PMSS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDDFR_Type_PMSS r v)


def _set_PMDEVID_Type_PMSS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMDEVID_Type_PMSS r v)


def _set_ID_AA64DFR0_EL1_Type_PMSVer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_PMSVer r v)


def _set_ID_AA64DFR0_EL1_Type_PMUVer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_PMUVer r v)


def _set_EDDFR_Type_PMUVer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDDFR_Type_PMUVer r v)


def _set_ID_AA64DFR0_EL1_Type_SEBEP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_SEBEP r v)


def _set_EDDFR_Type_SEBEP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDDFR_Type_SEBEP r v)


def _set_ID_AA64DFR0_EL1_Type_TraceBuffer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_TraceBuffer r v)


def _set_ID_AA64DFR0_EL1_Type_TraceFilt (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_TraceFilt r v)


def _set_EDDFR_Type_TraceFilt (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDDFR_Type_TraceFilt r v)


def _set_ID_DFR0_EL1_Type_TraceFilt (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_DFR0_EL1_Type_TraceFilt r v)


def _set_ID_DFR0_Type_TraceFilt (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_DFR0_Type_TraceFilt r v)


def _set_ID_AA64DFR0_EL1_Type_TraceVer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_TraceVer r v)


def _set_EDDFR_Type_TraceVer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDDFR_Type_TraceVer r v)


def _set_ID_AA64DFR0_EL1_Type_WRPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR0_EL1_Type_WRPs r v)


def _set_DBGDIDR_Type_WRPs (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDIDR_Type_WRPs r v)


def _set_EDDFR1_Type_WRPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDDFR1_Type_WRPs r v)


def _set_EDDFR_Type_WRPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDDFR_Type_WRPs r v)


def _set_ID_AA64DFR1_EL1_Type_WRPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR1_EL1_Type_WRPs r v)


def _set_ICV_BPR1_EL1_Type_BinaryPoint (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICV_BPR1_EL1_Type_BinaryPoint r v)


def _set_ICC_BPR0_EL1_Type_BinaryPoint (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_BPR0_EL1_Type_BinaryPoint r v)


def _set_ICC_BPR0_Type_BinaryPoint (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICC_BPR0_Type_BinaryPoint r v)


def _set_ICC_BPR1_EL1_Type_BinaryPoint (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_BPR1_EL1_Type_BinaryPoint r v)


def _set_ICC_BPR1_Type_BinaryPoint (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICC_BPR1_Type_BinaryPoint r v)


def _set_ICV_BPR0_EL1_Type_BinaryPoint (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICV_BPR0_EL1_Type_BinaryPoint r v)


def _set_ICV_BPR0_Type_BinaryPoint (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICV_BPR0_Type_BinaryPoint r v)


def _set_ICV_BPR1_Type_BinaryPoint (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICV_BPR1_Type_BinaryPoint r v)


def _set_ID_ISAR2_EL1_Type_LoadStore (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_ISAR2_EL1_Type_LoadStore r v)


def _set_ID_ISAR2_Type_LoadStore (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_ISAR2_Type_LoadStore r v)


def _set_ID_ISAR2_EL1_Type_MemHint (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_ISAR2_EL1_Type_MemHint r v)


def _set_ID_ISAR2_Type_MemHint (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_ISAR2_Type_MemHint r v)


def _set_ID_ISAR2_EL1_Type_Mult (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_ISAR2_EL1_Type_Mult r v)


def _set_ID_ISAR2_Type_Mult (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_ISAR2_Type_Mult r v)


def _set_ID_ISAR2_EL1_Type_MultS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_ISAR2_EL1_Type_MultS r v)


def _set_ID_ISAR2_Type_MultS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_ISAR2_Type_MultS r v)


def _set_ID_ISAR2_EL1_Type_MultU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_ISAR2_EL1_Type_MultU r v)


def _set_ID_ISAR2_Type_MultU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_ISAR2_Type_MultU r v)


def _set_ID_ISAR2_EL1_Type_MultiAccessInt (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_ISAR2_EL1_Type_MultiAccessInt r v)


def _set_ID_ISAR2_Type_MultiAccessInt (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_ISAR2_Type_MultiAccessInt r v)


def _set_ID_ISAR2_EL1_Type_PSR_AR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_ISAR2_EL1_Type_PSR_AR r v)


def _set_ID_ISAR2_Type_PSR_AR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_ISAR2_Type_PSR_AR r v)


def _set_ID_ISAR2_EL1_Type_Reversal (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_ISAR2_EL1_Type_Reversal r v)


def _set_ID_ISAR2_Type_Reversal (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_ISAR2_Type_Reversal r v)


def _set_PMECR_EL1_Type_KPME (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMECR_EL1_Type_KPME r v)


def _set_PMECR_EL1_Type_SSE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMECR_EL1_Type_SSE r v)


def _set_RMR_EL1_Type_AA64 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_RMR_EL1_Type_AA64 r v)


def _set_HRMR_Type_AA64 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HRMR_Type_AA64 r v)


def _set_RMR_EL2_Type_AA64 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_RMR_EL2_Type_AA64 r v)


def _set_RMR_EL3_Type_AA64 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_RMR_EL3_Type_AA64 r v)


def _set_RMR_Type_AA64 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_RMR_Type_AA64 r v)


def _set_RMR_EL1_Type_RR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_RMR_EL1_Type_RR r v)


def _set_HRMR_Type_RR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HRMR_Type_RR r v)


def _set_RMR_EL2_Type_RR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_RMR_EL2_Type_RR r v)


def _set_RMR_EL3_Type_RR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_RMR_EL3_Type_RR r v)


def _set_RMR_Type_RR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_RMR_Type_RR r v)


def _set_HAFGRTR_EL2_Type_AMCNTEN0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMCNTEN0 r v)


def _set_HAFGRTR_EL2_Type_AMCNTEN1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMCNTEN1 r v)


def _set_HAFGRTR_EL2_Type_AMEVCNTR00_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR00_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVCNTR01_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR01_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVCNTR02_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR02_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVCNTR03_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR03_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVCNTR10_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR10_EL0 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTR10_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR10_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVCNTR110_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR110_EL0 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTR110_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR110_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVCNTR111_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR111_EL0 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTR111_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR111_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVCNTR112_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR112_EL0 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTR112_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR112_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVCNTR113_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR113_EL0 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTR113_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR113_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVCNTR114_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR114_EL0 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTR114_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR114_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVCNTR115_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR115_EL0 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTR115_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR115_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVCNTR11_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR11_EL0 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTR11_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR11_EL0 r v)


end ArmFull.Functions
