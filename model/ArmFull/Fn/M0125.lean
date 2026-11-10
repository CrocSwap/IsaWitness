import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0058
import ArmFull.Fn.M0063
import ArmFull.Fn.M0064
import ArmFull.Fn.M0065

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

def _set_ID_AA64MMFR2_EL1_Type_CCIDX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_CCIDX r v)


def _set_ID_MMFR4_Type_CCIDX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR4_Type_CCIDX r v)


def _set_ID_MMFR4_EL1_Type_EVT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR4_EL1_Type_EVT r v)


def _set_ID_AA64MMFR2_EL1_Type_EVT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_EVT r v)


def _set_ID_MMFR4_Type_EVT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR4_Type_EVT r v)


def _set_ID_MMFR4_EL1_Type_HPDS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR4_EL1_Type_HPDS r v)


def _set_ID_AA64MMFR1_EL1_Type_HPDS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_HPDS r v)


def _set_ID_MMFR4_Type_HPDS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR4_Type_HPDS r v)


def _set_ID_MMFR4_EL1_Type_LSM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR4_EL1_Type_LSM r v)


def _set_ID_AA64MMFR2_EL1_Type_LSM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_LSM r v)


def _set_ID_MMFR4_Type_LSM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR4_Type_LSM r v)


def _set_ID_MMFR4_EL1_Type_SpecSEI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR4_EL1_Type_SpecSEI r v)


def _set_ID_AA64MMFR1_EL1_Type_SpecSEI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_SpecSEI r v)


def _set_ID_MMFR4_Type_SpecSEI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR4_Type_SpecSEI r v)


def _set_ID_MMFR4_EL1_Type_XNX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR4_EL1_Type_XNX r v)


def _set_ID_AA64MMFR1_EL1_Type_XNX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_XNX r v)


def _set_ID_MMFR4_Type_XNX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR4_Type_XNX r v)


def _set_ID_AA64MMFR2_EL1_Type_BBM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_BBM r v)


def _set_ID_AA64MMFR2_EL1_Type_E0PD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_E0PD r v)


def _set_ID_AA64MMFR2_EL1_Type_TTL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_TTL r v)


def _set_ID_AA64MMFR2_EL1_Type_VARange (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_VARange r v)


def _set_HDFGRTR_EL2_Type_DBGAUTHSTATUS_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_DBGAUTHSTATUS_EL1 r v)


def _set_HDFGRTR_EL2_Type_DBGBCRn_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_DBGBCRn_EL1 r v)


def _set_HDFGWTR_EL2_Type_DBGBCRn_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_DBGBCRn_EL1 r v)


def _set_HDFGRTR_EL2_Type_DBGBVRn_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_DBGBVRn_EL1 r v)


def _set_HDFGWTR_EL2_Type_DBGBVRn_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_DBGBVRn_EL1 r v)


def _set_HDFGRTR_EL2_Type_DBGCLAIM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_DBGCLAIM r v)


def _set_HDFGWTR_EL2_Type_DBGCLAIM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_DBGCLAIM r v)


def _set_HDFGRTR_EL2_Type_DBGPRCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_DBGPRCR_EL1 r v)


def _set_HDFGWTR_EL2_Type_DBGPRCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_DBGPRCR_EL1 r v)


def _set_HDFGRTR_EL2_Type_DBGWCRn_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_DBGWCRn_EL1 r v)


def _set_HDFGWTR_EL2_Type_DBGWCRn_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_DBGWCRn_EL1 r v)


def _set_HDFGRTR_EL2_Type_DBGWVRn_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_DBGWVRn_EL1 r v)


def _set_HDFGWTR_EL2_Type_DBGWVRn_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_DBGWVRn_EL1 r v)


def _set_HDFGRTR_EL2_Type_MDSCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_MDSCR_EL1 r v)


def _set_HDFGWTR_EL2_Type_MDSCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_MDSCR_EL1 r v)


def _set_HDFGRTR_EL2_Type_OSDLR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_OSDLR_EL1 r v)


def _set_HDFGWTR_EL2_Type_OSDLR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_OSDLR_EL1 r v)


def _set_HDFGRTR_EL2_Type_OSECCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_OSECCR_EL1 r v)


def _set_HDFGWTR_EL2_Type_OSECCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_OSECCR_EL1 r v)


def _set_HDFGRTR_EL2_Type_OSLSR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_OSLSR_EL1 r v)


def _set_HDFGRTR_EL2_Type_PMBIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMBIDR_EL1 r v)


def _set_HDFGRTR_EL2_Type_PMBLIMITR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMBLIMITR_EL1 r v)


def _set_HDFGWTR_EL2_Type_PMBLIMITR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMBLIMITR_EL1 r v)


def _set_HDFGRTR_EL2_Type_PMBPTR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMBPTR_EL1 r v)


def _set_HDFGWTR_EL2_Type_PMBPTR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMBPTR_EL1 r v)


def _set_HDFGRTR_EL2_Type_PMBSR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMBSR_EL1 r v)


def _set_HDFGWTR_EL2_Type_PMBSR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMBSR_EL1 r v)


def _set_HDFGRTR_EL2_Type_PMCCFILTR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMCCFILTR_EL0 r v)


def _set_HDFGWTR_EL2_Type_PMCCFILTR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMCCFILTR_EL0 r v)


def _set_HDFGRTR_EL2_Type_PMCCNTR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMCCNTR_EL0 r v)


def _set_HDFGWTR_EL2_Type_PMCCNTR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMCCNTR_EL0 r v)


def _set_HDFGRTR_EL2_Type_PMCEIDn_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMCEIDn_EL0 r v)


def _set_HDFGRTR_EL2_Type_PMCNTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMCNTEN r v)


def _set_HDFGWTR_EL2_Type_PMCNTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMCNTEN r v)


def _set_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 r v)


def _set_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 r v)


def _set_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 r v)


def _set_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 r v)


def _set_HDFGRTR_EL2_Type_PMINTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMINTEN r v)


def _set_HDFGWTR_EL2_Type_PMINTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMINTEN r v)


def _set_HDFGRTR_EL2_Type_PMMIR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMMIR_EL1 r v)


def _set_HDFGRTR_EL2_Type_PMOVS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMOVS r v)


def _set_HDFGWTR_EL2_Type_PMOVS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMOVS r v)


def _set_HDFGRTR_EL2_Type_PMSCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMSCR_EL1 r v)


def _set_HDFGWTR_EL2_Type_PMSCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMSCR_EL1 r v)


def _set_HDFGRTR_EL2_Type_PMSELR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMSELR_EL0 r v)


def _set_HDFGWTR_EL2_Type_PMSELR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMSELR_EL0 r v)


def _set_HDFGRTR_EL2_Type_PMSEVFR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMSEVFR_EL1 r v)


def _set_HDFGWTR_EL2_Type_PMSEVFR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMSEVFR_EL1 r v)


def _set_HDFGRTR_EL2_Type_PMSFCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMSFCR_EL1 r v)


def _set_HDFGWTR_EL2_Type_PMSFCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMSFCR_EL1 r v)


def _set_HDFGRTR_EL2_Type_PMSICR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMSICR_EL1 r v)


def _set_HDFGWTR_EL2_Type_PMSICR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMSICR_EL1 r v)


def _set_HDFGRTR_EL2_Type_PMSIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMSIDR_EL1 r v)


def _set_HDFGRTR_EL2_Type_PMSIRR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMSIRR_EL1 r v)


def _set_HDFGWTR_EL2_Type_PMSIRR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMSIRR_EL1 r v)


def _set_HDFGRTR_EL2_Type_PMSLATFR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMSLATFR_EL1 r v)


def _set_HDFGWTR_EL2_Type_PMSLATFR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMSLATFR_EL1 r v)


def _set_HDFGRTR_EL2_Type_PMUSERENR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_PMUSERENR_EL0 r v)


def _set_HDFGWTR_EL2_Type_PMUSERENR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_PMUSERENR_EL0 r v)


def _set_HDFGRTR_EL2_Type_TRC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRC r v)


def _set_HDFGWTR_EL2_Type_TRC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_TRC r v)


def _set_HDFGRTR_EL2_Type_TRCAUTHSTATUS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCAUTHSTATUS r v)


def _set_HDFGRTR_EL2_Type_TRCAUXCTLR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCAUXCTLR r v)


def _set_HDFGWTR_EL2_Type_TRCAUXCTLR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_TRCAUXCTLR r v)


def _set_HDFGRTR_EL2_Type_TRCCLAIM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCCLAIM r v)


def _set_HDFGWTR_EL2_Type_TRCCLAIM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_TRCCLAIM r v)


def _set_HDFGRTR_EL2_Type_TRCCNTVRn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCCNTVRn r v)


def _set_HDFGWTR_EL2_Type_TRCCNTVRn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_TRCCNTVRn r v)


def _set_HDFGRTR_EL2_Type_TRCID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCID r v)


def _set_HDFGRTR_EL2_Type_TRCIMSPECn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCIMSPECn r v)


def _set_HDFGWTR_EL2_Type_TRCIMSPECn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_TRCIMSPECn r v)


def _set_HDFGRTR_EL2_Type_TRCOSLSR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCOSLSR r v)


def _set_HDFGRTR_EL2_Type_TRCPRGCTLR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCPRGCTLR r v)


def _set_HDFGWTR_EL2_Type_TRCPRGCTLR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_TRCPRGCTLR r v)


def _set_HDFGRTR_EL2_Type_TRCSEQSTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCSEQSTR r v)


def _set_HDFGWTR_EL2_Type_TRCSEQSTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_TRCSEQSTR r v)


def _set_HDFGRTR_EL2_Type_TRCSSCSRn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCSSCSRn r v)


def _set_HDFGWTR_EL2_Type_TRCSSCSRn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_TRCSSCSRn r v)


def _set_HDFGRTR_EL2_Type_TRCSTATR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCSTATR r v)


def _set_HDFGRTR_EL2_Type_TRCVICTLR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_TRCVICTLR r v)


def _set_HDFGWTR_EL2_Type_TRCVICTLR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_TRCVICTLR r v)


def _set_HDFGRTR_EL2_Type_nBRBCTL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_nBRBCTL r v)


def _set_HDFGWTR_EL2_Type_nBRBCTL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_nBRBCTL r v)


def _set_HDFGRTR_EL2_Type_nBRBDATA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_nBRBDATA r v)


def _set_HDFGWTR_EL2_Type_nBRBDATA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_nBRBDATA r v)


def _set_HDFGRTR_EL2_Type_nBRBIDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_nBRBIDR r v)


def _set_HDFGRTR_EL2_Type_nPMSNEVFR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR_EL2_Type_nPMSNEVFR_EL1 r v)


def _set_HDFGWTR_EL2_Type_nPMSNEVFR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR_EL2_Type_nPMSNEVFR_EL1 r v)


def _set_ICV_NMIAR1_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICV_NMIAR1_EL1_Type_INTID r v)


def _set_GICC_AEOIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICC_AEOIR_Type_INTID r v)


def _set_GICC_AHPPIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICC_AHPPIR_Type_INTID r v)


def _set_GICC_AIAR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICC_AIAR_Type_INTID r v)


def _set_GICC_DIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICC_DIR_Type_INTID r v)


def _set_GICC_EOIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICC_EOIR_Type_INTID r v)


def _set_GICC_HPPIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICC_HPPIR_Type_INTID r v)


def _set_GICC_IAR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICC_IAR_Type_INTID r v)


def _set_GICD_CLRSPI_NSR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 13)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_CLRSPI_NSR_Type_INTID r v)


def _set_GICD_CLRSPI_SR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 13)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_CLRSPI_SR_Type_INTID r v)


def _set_GICD_SETSPI_NSR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 13)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_SETSPI_NSR_Type_INTID r v)


def _set_GICD_SETSPI_SR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 13)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_SETSPI_SR_Type_INTID r v)


def _set_GICD_SGIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_SGIR_Type_INTID r v)


def _set_GICM_CLRSPI_NSR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 13)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICM_CLRSPI_NSR_Type_INTID r v)


def _set_GICM_CLRSPI_SR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 13)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICM_CLRSPI_SR_Type_INTID r v)


def _set_GICM_SETSPI_NSR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 13)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICM_SETSPI_NSR_Type_INTID r v)


def _set_GICM_SETSPI_SR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 13)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICM_SETSPI_SR_Type_INTID r v)


def _set_GICM_TYPER_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 13)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICM_TYPER_Type_INTID r v)


def _set_GICR_INVLPIR_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_INVLPIR_Type_INTID r v)


def _set_GICV_AEOIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 25)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICV_AEOIR_Type_INTID r v)


def _set_GICV_AHPPIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 25)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICV_AHPPIR_Type_INTID r v)


def _set_GICV_AIAR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 25)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICV_AIAR_Type_INTID r v)


def _set_GICV_DIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 25)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICV_DIR_Type_INTID r v)


def _set_GICV_EOIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 25)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICV_EOIR_Type_INTID r v)


def _set_GICV_HPPIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 25)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICV_HPPIR_Type_INTID r v)


def _set_GICV_IAR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 25)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICV_IAR_Type_INTID r v)


def _set_ICC_ASGI1R_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_ASGI1R_EL1_Type_INTID r v)


def _set_ICC_ASGI1R_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_ASGI1R_Type_INTID r v)


def _set_ICC_DIR_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_DIR_EL1_Type_INTID r v)


def _set_ICC_DIR_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICC_DIR_Type_INTID r v)


def _set_ICC_EOIR0_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_EOIR0_EL1_Type_INTID r v)


def _set_ICC_EOIR0_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICC_EOIR0_Type_INTID r v)


def _set_ICC_EOIR1_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_EOIR1_EL1_Type_INTID r v)


def _set_ICC_EOIR1_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICC_EOIR1_Type_INTID r v)


def _set_ICC_HPPIR0_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_HPPIR0_EL1_Type_INTID r v)


def _set_ICC_HPPIR0_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICC_HPPIR0_Type_INTID r v)


def _set_ICC_HPPIR1_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_HPPIR1_EL1_Type_INTID r v)


def _set_ICC_HPPIR1_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICC_HPPIR1_Type_INTID r v)


def _set_ICC_IAR0_EL1_Type_INTID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_IAR0_EL1_Type_INTID r v)


def _set_ICC_IAR0_Type_INTID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICC_IAR0_Type_INTID r v)


end ArmFull.Functions
