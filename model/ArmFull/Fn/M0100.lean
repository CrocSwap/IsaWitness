import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0018
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0025

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

def _set_TRFCR_Type_TS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_TRFCR_Type_TS r v)


def _set_ERRnFR_ElemType_UC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ERRnFR_ElemType_UC r v)


def _set_ERRnFR_ElemType_UE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ERRnFR_ElemType_UE r v)


def _set_ERRnFR_ElemType_UEO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ERRnFR_ElemType_UEO r v)


def _set_ERRnFR_ElemType_UER (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ERRnFR_ElemType_UER r v)


def _set_ERRnFR_ElemType_UEU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ERRnFR_ElemType_UEU r v)


def _set_ERRnFR_ElemType_UI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ERRnFR_ElemType_UI r v)


def _set_CTR_EL0_Type_CWG (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CTR_EL0_Type_CWG r v)


def _set_CTR_Type_CWG (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTR_Type_CWG r v)


def _set_CTR_EL0_Type_DIC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CTR_EL0_Type_DIC r v)


def _set_CTR_Type_DIC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTR_Type_DIC r v)


def _set_CTR_EL0_Type_DminLine (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CTR_EL0_Type_DminLine r v)


def _set_CTR_Type_DminLine (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTR_Type_DminLine r v)


def _set_CTR_EL0_Type_ERG (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CTR_EL0_Type_ERG r v)


def _set_CTR_Type_ERG (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTR_Type_ERG r v)


def _set_CTR_EL0_Type_IminLine (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CTR_EL0_Type_IminLine r v)


def _set_CTR_Type_IminLine (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTR_Type_IminLine r v)


def _set_CTR_EL0_Type_L1Ip (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CTR_EL0_Type_L1Ip r v)


def _set_CTR_Type_L1Ip (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTR_Type_L1Ip r v)


def _set_CTR_EL0_Type_TminLine (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CTR_EL0_Type_TminLine r v)


def _set_HDCR_Type_HCCD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HDCR_Type_HCCD r v)


def _set_MDCR_EL2_Type_HCCD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL2_Type_HCCD r v)


def _set_HDCR_Type_HLP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HDCR_Type_HLP r v)


def _set_MDCR_EL2_Type_HLP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL2_Type_HLP r v)


def _set_HDCR_Type_HPMD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HDCR_Type_HPMD r v)


def _set_MDCR_EL2_Type_HPMD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL2_Type_HPMD r v)


def _set_HDCR_Type_HPME (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HDCR_Type_HPME r v)


def _set_MDCR_EL2_Type_HPME (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL2_Type_HPME r v)


def _set_HDCR_Type_HPMFZO (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HDCR_Type_HPMFZO r v)


def _set_MDCR_EL2_Type_HPMFZO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL2_Type_HPMFZO r v)


def _set_HDCR_Type_HPMN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HDCR_Type_HPMN r v)


def _set_MDCR_EL2_Type_HPMN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL2_Type_HPMN r v)


def _set_HDCR_Type_MTPME (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HDCR_Type_MTPME r v)


def _set_MDCR_EL2_Type_MTPME (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL2_Type_MTPME r v)


def _set_MDCR_EL3_Type_MTPME (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL3_Type_MTPME r v)


def _set_SDCR_Type_MTPME (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SDCR_Type_MTPME r v)


def _set_HDCR_Type_TDA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HDCR_Type_TDA r v)


def _set_DBGDSCRext_Type_TDA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDSCRext_Type_TDA r v)


def _set_EDSCR_Type_TDA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDSCR_Type_TDA r v)


def _set_MDCR_EL2_Type_TDA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL2_Type_TDA r v)


def _set_MDCR_EL3_Type_TDA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL3_Type_TDA r v)


def _set_MDSCR_EL1_Type_TDA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDSCR_EL1_Type_TDA r v)


def _set_HDCR_Type_TDCC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HDCR_Type_TDCC r v)


def _set_MDCR_EL2_Type_TDCC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL2_Type_TDCC r v)


def _set_MDCR_EL3_Type_TDCC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL3_Type_TDCC r v)


def _set_MDSCR_EL1_Type_TDCC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDSCR_EL1_Type_TDCC r v)


def _set_SDCR_Type_TDCC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SDCR_Type_TDCC r v)


def _set_HDCR_Type_TDE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HDCR_Type_TDE r v)


def _set_MDCR_EL2_Type_TDE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL2_Type_TDE r v)


def _set_HDCR_Type_TDOSA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HDCR_Type_TDOSA r v)


def _set_MDCR_EL2_Type_TDOSA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL2_Type_TDOSA r v)


def _set_MDCR_EL3_Type_TDOSA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL3_Type_TDOSA r v)


def _set_HDCR_Type_TDRA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HDCR_Type_TDRA r v)


def _set_MDCR_EL2_Type_TDRA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL2_Type_TDRA r v)


def _set_HDCR_Type_TPM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HDCR_Type_TPM r v)


def _set_MDCR_EL2_Type_TPM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL2_Type_TPM r v)


def _set_MDCR_EL3_Type_TPM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL3_Type_TPM r v)


def _set_HDCR_Type_TPMCR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HDCR_Type_TPMCR r v)


def _set_MDCR_EL2_Type_TPMCR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL2_Type_TPMCR r v)


def _set_HDCR_Type_TTRF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HDCR_Type_TTRF r v)


def _set_MDCR_EL2_Type_TTRF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL2_Type_TTRF r v)


def _set_MDCR_EL3_Type_TTRF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL3_Type_TTRF r v)


def _set_SDCR_Type_TTRF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SDCR_Type_TTRF r v)


def _set_MDCR_EL2_Type_E2PB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL2_Type_E2PB r v)


def _set_MDCR_EL2_Type_EBWE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL2_Type_EBWE r v)


def _set_MDCR_EL3_Type_EBWE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL3_Type_EBWE r v)


def _set_MDCR_EL2_Type_EnSPM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL2_Type_EnSPM r v)


def _set_MDSCR_EL1_Type_EnSPM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDSCR_EL1_Type_EnSPM r v)


def _set_MDCR_EL2_Type_HPMFZS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL2_Type_HPMFZS r v)


def _set_MDCR_EL2_Type_PMEE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL2_Type_PMEE r v)


def _set_MDCR_EL3_Type_PMEE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL3_Type_PMEE r v)


def _set_PMECR_EL1_Type_PMEE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMECR_EL1_Type_PMEE r v)


def _set_MDCR_EL2_Type_PMSSE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL2_Type_PMSSE r v)


def _set_MDCR_EL3_Type_PMSSE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL3_Type_PMSSE r v)


def _set_MDCR_EL2_Type_TPMS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL2_Type_TPMS r v)


/-- Type quantifiers: high : Int, low : Int -/
def ConstrainUnpredictableInteger (low : Int) (high : Int) (which : Unpredictable) : SailM (Constraint × Int) := do
  ArmFull.assert (low ≤b high) "armcert/armcert_c27b.sail:424.22-424.23"
  let c ← (( do (undefined_Constraint (← occLabel 496) ()) ) : SailM Constraint )
  let c ← (( do
    if ((BEq.beq which Unpredictable_BPNOTIMPL) : Bool)
    then
      (do
        let w__0 ← (( do (undefined_bool_at (← occLabel 498) ()) ) : SailM Bool )
        let w__1 : Constraint :=
          if ((w__0 : Bool) : Bool)
          then Constraint_DISABLED
          else Constraint_UNKNOWN
        (pure ((w__1 : Constraint))))
    else
      (do
        if (((BEq.beq which Unpredictable_BPNOTCTXCMP) || ((BEq.beq which Unpredictable_RESBPMASK) || (BEq.beq
                 which Unpredictable_RESWPMASK))) : Bool)
        then
          (do
            let tag ← (( do
              ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 497) 0 2)))
              ) : SailM Nat )
            let c : Constraint :=
              if ((tag == 0) : Bool)
              then Constraint_DISABLED
              else
                (if ((tag == 1) : Bool)
                then Constraint_NONE
                else Constraint_UNKNOWN)
            (pure (c)))
        else (pure (c))) ) : SailM Constraint )
  let value_name ← (( do (undefined_range_at (← occLabel 499) low high) ) : SailM Int )
  (pure ((c, value_name)))


def _set_EDSCR_Type_ERR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDSCR_Type_ERR r v)


def _set_DBGDSCRext_Type_ERR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDSCRext_Type_ERR r v)


def _set_MDSCR_EL1_Type_ERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDSCR_EL1_Type_ERR r v)


def _set_EDSCR_Type_HDE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDSCR_Type_HDE r v)


def _set_DBGDSCRext_Type_HDE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDSCRext_Type_HDE r v)


def _set_MDSCR_EL1_Type_HDE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDSCR_EL1_Type_HDE r v)


def _set_EDSCR_Type_INTdis (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDSCR_Type_INTdis r v)


def _set_DBGDSCRext_Type_INTdis (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDSCRext_Type_INTdis r v)


def _set_MDSCR_EL1_Type_INTdis (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDSCR_EL1_Type_INTdis r v)


def _set_EDSCR_Type_ITE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDSCR_Type_ITE r v)


def _set_EDDFR1_Type_ITE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDDFR1_Type_ITE r v)


def _set_ID_AA64DFR1_EL1_Type_ITE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR1_EL1_Type_ITE r v)


def _set_EDSCR_Type_ITO (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDSCR_Type_ITO r v)


def _set_EDSCR_Type_MA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDSCR_Type_MA r v)


def _set_EDSCR_Type_PipeAdv (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDSCR_Type_PipeAdv r v)


def _set_EDSCR_Type_RXO (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDSCR_Type_RXO r v)


def _set_DBGDSCRext_Type_RXO (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDSCRext_Type_RXO r v)


def _set_MDSCR_EL1_Type_RXO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDSCR_EL1_Type_RXO r v)


def _set_EDSCR_Type_RXfull (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDSCR_Type_RXfull r v)


def _set_DBGDSCRext_Type_RXfull (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDSCRext_Type_RXfull r v)


def _set_DBGDSCRint_Type_RXfull (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDSCRint_Type_RXfull r v)


def _set_MDCCSR_EL0_Type_RXfull (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCCSR_EL0_Type_RXfull r v)


def _set_MDSCR_EL1_Type_RXfull (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDSCR_EL1_Type_RXfull r v)


def _set_EDSCR_Type_SC2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDSCR_Type_SC2 r v)


def _set_DBGDSCRext_Type_SC2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDSCRext_Type_SC2 r v)


def _set_MDSCR_EL1_Type_SC2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDSCR_EL1_Type_SC2 r v)


def _set_EDSCR_Type_SDD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDSCR_Type_SDD r v)


def _set_MDCR_EL3_Type_SDD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCR_EL3_Type_SDD r v)


def _set_EDSCR_Type_STATUS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 6)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDSCR_Type_STATUS r v)


def _set_DFSR_Type_STATUS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 6)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DFSR_Type_STATUS r v)


def _set_DISR_Type_STATUS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 6)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DISR_Type_STATUS r v)


def _set_IFSR32_EL2_Type_STATUS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_IFSR32_EL2_Type_STATUS r v)


def _set_IFSR_Type_STATUS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 6)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_IFSR_Type_STATUS r v)


def _set_VDISR_EL2_Type_STATUS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VDISR_EL2_Type_STATUS r v)


def _set_VDISR_Type_STATUS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 6)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_VDISR_Type_STATUS r v)


def _set_EDSCR_Type_TFO (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDSCR_Type_TFO r v)


def _set_DBGDSCRext_Type_TFO (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDSCRext_Type_TFO r v)


def _set_MDSCR_EL1_Type_TFO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDSCR_EL1_Type_TFO r v)


def _set_EDSCR_Type_TXU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDSCR_Type_TXU r v)


def _set_DBGDSCRext_Type_TXU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDSCRext_Type_TXU r v)


def _set_MDSCR_EL1_Type_TXU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDSCR_EL1_Type_TXU r v)


def _set_EDSCR_Type_TXfull (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDSCR_Type_TXfull r v)


def _set_DBGDSCRext_Type_TXfull (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDSCRext_Type_TXfull r v)


def _set_DBGDSCRint_Type_TXfull (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDSCRint_Type_TXfull r v)


def _set_MDCCSR_EL0_Type_TXfull (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDCCSR_EL0_Type_TXfull r v)


def _set_MDSCR_EL1_Type_TXfull (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDSCR_EL1_Type_TXfull r v)


def Halted (_ : Unit) : SailM Bool := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
         (pure ((((_get_EDSCR_Type_STATUS w__0) == 0b000001#6) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
        (pure ((((_get_EDSCR_Type_STATUS w__1) == 0b000010#6) : Bool)))) ) : SailM Bool )
  (pure ((! w__2)))


def _set_PMCNTENCLR_EL0_Type_F0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_F0 r v)


def _set_PMCNTENSET_EL0_Type_F0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMCNTENSET_EL0_Type_F0 r v)


def _set_PMCNTEN_Type_F0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMCNTEN_Type_F0 r v)


def _set_PMINTENCLR_EL1_Type_F0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMINTENCLR_EL1_Type_F0 r v)


def _set_PMINTENSET_EL1_Type_F0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMINTENSET_EL1_Type_F0 r v)


def _set_PMINTEN_Type_F0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMINTEN_Type_F0 r v)


def _set_PMOVSCLR_EL0_Type_F0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMOVSCLR_EL0_Type_F0 r v)


def _set_PMOVSSET_EL0_Type_F0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMOVSSET_EL0_Type_F0 r v)


def _set_PMOVS_Type_F0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMOVS_Type_F0 r v)


def _set_PMUACR_EL1_Type_F0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMUACR_EL1_Type_F0 r v)


def _set_PMZR_EL0_Type_F0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMZR_EL0_Type_F0 r v)


def _set_PMCNTENCLR_EL0_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMCNTENCLR_EL0_Type_P0 r v)


def _set_AMCNTENCLR0_EL0_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCNTENCLR0_EL0_Type_P0 r v)


def _set_AMCNTENCLR0_Type_P0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCNTENCLR0_Type_P0 r v)


def _set_AMCNTENCLR1_EL0_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCNTENCLR1_EL0_Type_P0 r v)


def _set_AMCNTENCLR1_Type_P0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCNTENCLR1_Type_P0 r v)


def _set_AMCNTENSET0_EL0_Type_P0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCNTENSET0_EL0_Type_P0 r v)


def _set_AMCNTENSET0_Type_P0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCNTENSET0_Type_P0 r v)


end ArmFull.Functions
