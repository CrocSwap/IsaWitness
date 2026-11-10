import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0024
import ArmFull.Fn.M0042
import ArmFull.Fn.M0058
import ArmFull.Fn.M0072
import ArmFull.Fn.M0073

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

def _set_HFGRTR_EL2_Type_ERXPFGCDN_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_ERXPFGCDN_EL1 r v)


def _set_HFGWTR_EL2_Type_ERXPFGCTL_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_ERXPFGCTL_EL1 r v)


def _set_HFGRTR_EL2_Type_ERXPFGCTL_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_ERXPFGCTL_EL1 r v)


def _set_HFGWTR_EL2_Type_ERXSTATUS_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_ERXSTATUS_EL1 r v)


def _set_HFGRTR_EL2_Type_ERXSTATUS_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_ERXSTATUS_EL1 r v)


def _set_HFGWTR_EL2_Type_ESR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_ESR_EL1 r v)


def _set_HFGRTR_EL2_Type_ESR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_ESR_EL1 r v)


def _set_HFGWTR_EL2_Type_FAR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_FAR_EL1 r v)


def _set_HFGRTR_EL2_Type_FAR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_FAR_EL1 r v)


def _set_HFGWTR_EL2_Type_ICC_IGRPENn_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_ICC_IGRPENn_EL1 r v)


def _set_HFGRTR_EL2_Type_ICC_IGRPENn_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_ICC_IGRPENn_EL1 r v)


def _set_HFGWTR_EL2_Type_LORC_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_LORC_EL1 r v)


def _set_HFGRTR_EL2_Type_LORC_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_LORC_EL1 r v)


def _set_HFGWTR_EL2_Type_LOREA_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_LOREA_EL1 r v)


def _set_HFGRTR_EL2_Type_LOREA_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_LOREA_EL1 r v)


def _set_HFGWTR_EL2_Type_LORN_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_LORN_EL1 r v)


def _set_HFGRTR_EL2_Type_LORN_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_LORN_EL1 r v)


def _set_HFGWTR_EL2_Type_LORSA_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_LORSA_EL1 r v)


def _set_HFGRTR_EL2_Type_LORSA_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_LORSA_EL1 r v)


def _set_HFGWTR_EL2_Type_MAIR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_MAIR_EL1 r v)


def _set_HFGRTR_EL2_Type_MAIR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_MAIR_EL1 r v)


def _set_HFGWTR_EL2_Type_PAR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_PAR_EL1 r v)


def _set_HFGRTR_EL2_Type_PAR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_PAR_EL1 r v)


def _set_HFGWTR_EL2_Type_SCTLR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_SCTLR_EL1 r v)


def _set_HFGRTR_EL2_Type_SCTLR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_SCTLR_EL1 r v)


def _set_HFGWTR_EL2_Type_SCXTNUM_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_SCXTNUM_EL0 r v)


def _set_HFGRTR_EL2_Type_SCXTNUM_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_SCXTNUM_EL0 r v)


def _set_HFGWTR_EL2_Type_SCXTNUM_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_SCXTNUM_EL1 r v)


def _set_HFGRTR_EL2_Type_SCXTNUM_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_SCXTNUM_EL1 r v)


def _set_HFGWTR_EL2_Type_TCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_TCR_EL1 r v)


def _set_HFGRTR_EL2_Type_TCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_TCR_EL1 r v)


def _set_HFGWTR_EL2_Type_TPIDRRO_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_TPIDRRO_EL0 r v)


def _set_HFGRTR_EL2_Type_TPIDRRO_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_TPIDRRO_EL0 r v)


def _set_HFGWTR_EL2_Type_TPIDR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_TPIDR_EL0 r v)


def _set_HFGRTR_EL2_Type_TPIDR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_TPIDR_EL0 r v)


def _set_HFGWTR_EL2_Type_TPIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_TPIDR_EL1 r v)


def _set_HFGRTR_EL2_Type_TPIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_TPIDR_EL1 r v)


def _set_HFGWTR_EL2_Type_TTBR0_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_TTBR0_EL1 r v)


def _set_HFGRTR_EL2_Type_TTBR0_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_TTBR0_EL1 r v)


def _set_HFGWTR_EL2_Type_TTBR1_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_TTBR1_EL1 r v)


def _set_HFGRTR_EL2_Type_TTBR1_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_TTBR1_EL1 r v)


def _set_HFGWTR_EL2_Type_VBAR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_VBAR_EL1 r v)


def _set_HFGRTR_EL2_Type_VBAR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_VBAR_EL1 r v)


def _set_HFGWTR_EL2_Type_nACCDATA_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nACCDATA_EL1 r v)


def _set_HFGRTR_EL2_Type_nACCDATA_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nACCDATA_EL1 r v)


def _set_HFGWTR_EL2_Type_nAMAIR2_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nAMAIR2_EL1 r v)


def _set_HFGRTR_EL2_Type_nAMAIR2_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nAMAIR2_EL1 r v)


def _set_HFGWTR_EL2_Type_nGCS_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nGCS_EL0 r v)


def _set_HFGRTR_EL2_Type_nGCS_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nGCS_EL0 r v)


def _set_HFGWTR_EL2_Type_nGCS_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nGCS_EL1 r v)


def _set_HFGRTR_EL2_Type_nGCS_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nGCS_EL1 r v)


def _set_HFGWTR_EL2_Type_nMAIR2_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nMAIR2_EL1 r v)


def _set_HFGRTR_EL2_Type_nMAIR2_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nMAIR2_EL1 r v)


def _set_HFGWTR_EL2_Type_nPIRE0_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nPIRE0_EL1 r v)


def _set_HFGRTR_EL2_Type_nPIRE0_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nPIRE0_EL1 r v)


def _set_HFGWTR_EL2_Type_nPIR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nPIR_EL1 r v)


def _set_HFGRTR_EL2_Type_nPIR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nPIR_EL1 r v)


def _set_HFGWTR_EL2_Type_nPOR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nPOR_EL0 r v)


def _set_HFGRTR_EL2_Type_nPOR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nPOR_EL0 r v)


def _set_HFGWTR_EL2_Type_nPOR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nPOR_EL1 r v)


def _set_HFGRTR_EL2_Type_nPOR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nPOR_EL1 r v)


def _set_HFGWTR_EL2_Type_nRCWMASK_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nRCWMASK_EL1 r v)


def _set_HFGRTR_EL2_Type_nRCWMASK_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nRCWMASK_EL1 r v)


def _set_HFGWTR_EL2_Type_nS2POR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nS2POR_EL1 r v)


def _set_HFGRTR_EL2_Type_nS2POR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nS2POR_EL1 r v)


def _set_HFGWTR_EL2_Type_nSMPRI_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nSMPRI_EL1 r v)


def _set_HFGRTR_EL2_Type_nSMPRI_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nSMPRI_EL1 r v)


def _set_HFGWTR_EL2_Type_nTPIDR2_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR_EL2_Type_nTPIDR2_EL0 r v)


def _set_HFGRTR_EL2_Type_nTPIDR2_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_nTPIDR2_EL0 r v)


def _set_PMUSERENR_EL0_Type_CR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMUSERENR_EL0_Type_CR r v)


def _set_PMUSERENR_Type_CR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMUSERENR_Type_CR r v)


def _set_PMUSERENR_EL0_Type_ER (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMUSERENR_EL0_Type_ER r v)


def _set_PMUSERENR_Type_ER (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMUSERENR_Type_ER r v)


def _set_PMUSERENR_EL0_Type_IR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMUSERENR_EL0_Type_IR r v)


def _set_GICR_CTLR_Type_IR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_CTLR_Type_IR r v)


def _set_PMUSERENR_EL0_Type_TID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMUSERENR_EL0_Type_TID r v)


def _set_PMUSERENR_Type_TID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMUSERENR_Type_TID r v)


def _set_PMUSERENR_EL0_Type_UEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMUSERENR_EL0_Type_UEN r v)


def _set_PMCFGR_Type_UEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMCFGR_Type_UEN r v)


def __set_MDSCR_EL1 (value_name : (BitVec 64)) : SailM Unit := do
  let r : MDSCR_EL1_Type := value_name
  let w__0 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__0 5 0 (BitVec.slice r 0 6))
  let w__1 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__1 13 7 (BitVec.slice r 7 7))
  let w__2 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__2 18 15 (BitVec.slice r 15 4))
  let w__3 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (BitVec.update w__3 20 (Bit (BitVec.slice r 20 1)))
  let w__4 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__4 25 24 (BitVec.slice r 24 2))
  let w__5 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (BitVec.update w__5 28 (Bit (BitVec.slice r 28 1)))
  let w__6 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__6 34 32 (BitVec.slice r 32 3))
  let w__7 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__7 63 36 (BitVec.slice r 36 28))
  let w__8 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
  if ((! ((_get_OSLSR_EL1_Type_OSLK w__8) == 0#1)) : Bool)
  then
    (do
      let w__9 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
      writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__9 35 35 (_get_MDSCR_EL1_Type_EHBWE r)))
  else (pure (()))
  let w__10 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
  if (((_get_OSLSR_EL1_Type_OSLK w__10) == 1#1) : Bool)
  then
    (do
      let w__11 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
      writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__11 31 31 (_get_MDSCR_EL1_Type_TFO r)))
  else (pure (()))
  let w__12 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
  if (((_get_OSLSR_EL1_Type_OSLK w__12) == 1#1) : Bool)
  then
    (do
      let w__13 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
      writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__13 30 30 (_get_MDSCR_EL1_Type_RXfull r)))
  else (pure (()))
  let w__14 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
  if (((_get_OSLSR_EL1_Type_OSLK w__14) == 1#1) : Bool)
  then
    (do
      let w__15 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
      writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__15 29 29 (_get_MDSCR_EL1_Type_TXfull r)))
  else (pure (()))
  let w__16 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
  if (((_get_OSLSR_EL1_Type_OSLK w__16) == 1#1) : Bool)
  then
    (do
      let w__17 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
      writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__17 27 27 (_get_MDSCR_EL1_Type_RXO r)))
  else (pure (()))
  let w__18 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
  if (((_get_OSLSR_EL1_Type_OSLK w__18) == 1#1) : Bool)
  then
    (do
      let w__19 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
      writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__19 26 26 (_get_MDSCR_EL1_Type_TXU r)))
  else (pure (()))
  let w__20 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
  if (((_get_OSLSR_EL1_Type_OSLK w__20) == 1#1) : Bool)
  then
    (do
      let w__21 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
      writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__21 23 22 (_get_MDSCR_EL1_Type_INTdis r)))
  else (pure (()))
  let w__22 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
  if (((_get_OSLSR_EL1_Type_OSLK w__22) == 1#1) : Bool)
  then
    (do
      let w__23 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
      writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__23 21 21 (_get_MDSCR_EL1_Type_TDA r)))
  else (pure (()))
  let w__24 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
  if (((_get_OSLSR_EL1_Type_OSLK w__24) == 1#1) : Bool)
  then
    (do
      let w__25 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
      writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__25 19 19 (_get_MDSCR_EL1_Type_SC2 r)))
  else (pure (()))
  let w__26 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
  if (((_get_OSLSR_EL1_Type_OSLK w__26) == 1#1) : Bool)
  then
    (do
      let w__27 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
      writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__27 14 14 (_get_MDSCR_EL1_Type_HDE r)))
  else (pure (()))
  let w__28 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
  if (((_get_OSLSR_EL1_Type_OSLK w__28) == 1#1) : Bool)
  then
    (do
      let w__29 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
      writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__29 6 6 (_get_MDSCR_EL1_Type_ERR r)))
  else (pure (()))


def _set_ID_PFR0_EL1_Type_State0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_PFR0_EL1_Type_State0 r v)


def _set_ID_PFR0_Type_State0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_PFR0_Type_State0 r v)


def _set_ID_PFR0_EL1_Type_State1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_PFR0_EL1_Type_State1 r v)


def _set_ID_PFR0_Type_State1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_PFR0_Type_State1 r v)


def _set_ID_PFR0_EL1_Type_State2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_PFR0_EL1_Type_State2 r v)


def _set_ID_PFR0_Type_State2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_PFR0_Type_State2 r v)


def _set_ID_PFR0_EL1_Type_State3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_PFR0_EL1_Type_State3 r v)


def _set_ID_PFR0_Type_State3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_PFR0_Type_State3 r v)


def _set_MVFR1_EL1_Type_FPDNaN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MVFR1_EL1_Type_FPDNaN r v)


def _set_MVFR1_Type_FPDNaN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MVFR1_Type_FPDNaN r v)


def _set_MVFR1_EL1_Type_FPFtZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MVFR1_EL1_Type_FPFtZ r v)


def _set_MVFR1_Type_FPFtZ (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MVFR1_Type_FPFtZ r v)


def _set_MVFR1_EL1_Type_FPHP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MVFR1_EL1_Type_FPHP r v)


def _set_MVFR1_Type_FPHP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MVFR1_Type_FPHP r v)


def _set_MVFR1_EL1_Type_SIMDFMAC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MVFR1_EL1_Type_SIMDFMAC r v)


def _set_MVFR1_Type_SIMDFMAC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MVFR1_Type_SIMDFMAC r v)


def _set_MVFR1_EL1_Type_SIMDHP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MVFR1_EL1_Type_SIMDHP r v)


def _set_MVFR1_Type_SIMDHP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MVFR1_Type_SIMDHP r v)


def _set_MVFR1_EL1_Type_SIMDInt (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MVFR1_EL1_Type_SIMDInt r v)


def _set_MVFR1_Type_SIMDInt (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MVFR1_Type_SIMDInt r v)


def _set_MVFR1_EL1_Type_SIMDLS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MVFR1_EL1_Type_SIMDLS r v)


def _set_MVFR1_Type_SIMDLS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MVFR1_Type_SIMDLS r v)


def _set_MVFR1_EL1_Type_SIMDSP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MVFR1_EL1_Type_SIMDSP r v)


def _set_MVFR1_Type_SIMDSP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MVFR1_Type_SIMDSP r v)


def _set_HDFGWTR2_EL2_Type_nMDSELR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nMDSELR_EL1 r v)


def _set_HDFGRTR2_EL2_Type_nMDSELR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nMDSELR_EL1 r v)


def _set_HDFGWTR2_EL2_Type_nPMECR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nPMECR_EL1 r v)


def _set_HDFGRTR2_EL2_Type_nPMECR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nPMECR_EL1 r v)


def _set_HDFGWTR2_EL2_Type_nPMIAR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nPMIAR_EL1 r v)


def _set_HDFGRTR2_EL2_Type_nPMIAR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nPMIAR_EL1 r v)


def _set_HDFGWTR2_EL2_Type_nPMICFILTR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nPMICFILTR_EL0 r v)


def _set_HDFGRTR2_EL2_Type_nPMICFILTR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nPMICFILTR_EL0 r v)


def _set_HDFGWTR2_EL2_Type_nPMICNTR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nPMICNTR_EL0 r v)


def _set_HDFGRTR2_EL2_Type_nPMICNTR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nPMICNTR_EL0 r v)


def _set_HDFGWTR2_EL2_Type_nPMSDSFR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nPMSDSFR_EL1 r v)


def _set_HDFGRTR2_EL2_Type_nPMSDSFR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nPMSDSFR_EL1 r v)


def _set_HDFGWTR2_EL2_Type_nPMSSCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nPMSSCR_EL1 r v)


def _set_HDFGRTR2_EL2_Type_nPMSSCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nPMSSCR_EL1 r v)


def _set_HDFGWTR2_EL2_Type_nPMUACR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nPMUACR_EL1 r v)


def _set_HDFGRTR2_EL2_Type_nPMUACR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nPMUACR_EL1 r v)


def _set_HDFGWTR2_EL2_Type_nPMZR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nPMZR_EL0 r v)


def _set_HDFGWTR2_EL2_Type_nSPMACCESSR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nSPMACCESSR_EL1 r v)


def _set_HDFGRTR2_EL2_Type_nSPMACCESSR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nSPMACCESSR_EL1 r v)


def _set_HDFGWTR2_EL2_Type_nSPMCNTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nSPMCNTEN r v)


def _set_HDFGRTR2_EL2_Type_nSPMCNTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nSPMCNTEN r v)


def _set_HDFGWTR2_EL2_Type_nSPMCR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nSPMCR_EL0 r v)


def _set_HDFGRTR2_EL2_Type_nSPMCR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nSPMCR_EL0 r v)


end ArmFull.Functions
