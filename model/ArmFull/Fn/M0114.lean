import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0044
import ArmFull.Fn.M0045

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

def _set_MPAMIDR_EL1_Type_HAS_FORCE_NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMIDR_EL1_Type_HAS_FORCE_NS r v)


def _set_MPAMIDR_EL1_Type_HAS_HCR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMIDR_EL1_Type_HAS_HCR r v)


def _set_MPAMIDR_EL1_Type_HAS_SDEFLT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMIDR_EL1_Type_HAS_SDEFLT r v)


def _set_MPAMIDR_EL1_Type_HAS_TIDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMIDR_EL1_Type_HAS_TIDR r v)


def _set_MPAMIDR_EL1_Type_PARTID_MAX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMIDR_EL1_Type_PARTID_MAX r v)


def _set_MPAMIDR_EL1_Type_PMG_MAX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMIDR_EL1_Type_PMG_MAX r v)


def _set_MPAMIDR_EL1_Type_SP4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMIDR_EL1_Type_SP4 r v)


def _set_MPAMIDR_EL1_Type_VPMR_MAX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMIDR_EL1_Type_VPMR_MAX r v)


def _set_MPAMHCR_EL2_Type_EL0_VPMEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMHCR_EL2_Type_EL0_VPMEN r v)


def _set_MPAMHCR_EL2_Type_EL1_VPMEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMHCR_EL2_Type_EL1_VPMEN r v)


def _set_MPAMHCR_EL2_Type_GSTAPP_PLK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMHCR_EL2_Type_GSTAPP_PLK r v)


def _set_MPAMHCR_EL2_Type_TRAP_MPAMIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMHCR_EL2_Type_TRAP_MPAMIDR_EL1 r v)


def _set_MPAMVPM0_EL2_Type_PhyPARTID0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM0_EL2_Type_PhyPARTID0 r v)


def _set_MPAMVPM0_EL2_Type_PhyPARTID1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM0_EL2_Type_PhyPARTID1 r v)


def _set_MPAMVPM0_EL2_Type_PhyPARTID2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM0_EL2_Type_PhyPARTID2 r v)


def _set_MPAMVPM0_EL2_Type_PhyPARTID3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM0_EL2_Type_PhyPARTID3 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V0 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V1 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V10 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V11 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V12 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V13 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V14 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V15 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V16 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V17 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V18 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V19 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V2 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V20 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V21 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V22 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V23 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V24 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V25 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V26 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V27 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V28 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V29 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V3 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V30 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V31 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V4 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V5 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V6 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V7 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V8 r v)


def _set_MPAMVPMV_EL2_Type_VPM_V9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPMV_EL2_Type_VPM_V9 r v)


def _set_MPAMVPM1_EL2_Type_PhyPARTID4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM1_EL2_Type_PhyPARTID4 r v)


def _set_MPAMVPM1_EL2_Type_PhyPARTID5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM1_EL2_Type_PhyPARTID5 r v)


def _set_MPAMVPM1_EL2_Type_PhyPARTID6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM1_EL2_Type_PhyPARTID6 r v)


def _set_MPAMVPM1_EL2_Type_PhyPARTID7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM1_EL2_Type_PhyPARTID7 r v)


def _set_MPAMVPM2_EL2_Type_PhyPARTID10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM2_EL2_Type_PhyPARTID10 r v)


def _set_MPAMVPM2_EL2_Type_PhyPARTID11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM2_EL2_Type_PhyPARTID11 r v)


def _set_MPAMVPM2_EL2_Type_PhyPARTID8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM2_EL2_Type_PhyPARTID8 r v)


def _set_MPAMVPM2_EL2_Type_PhyPARTID9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM2_EL2_Type_PhyPARTID9 r v)


def _set_MPAMVPM3_EL2_Type_PhyPARTID12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM3_EL2_Type_PhyPARTID12 r v)


def _set_MPAMVPM3_EL2_Type_PhyPARTID13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM3_EL2_Type_PhyPARTID13 r v)


def _set_MPAMVPM3_EL2_Type_PhyPARTID14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM3_EL2_Type_PhyPARTID14 r v)


def _set_MPAMVPM3_EL2_Type_PhyPARTID15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM3_EL2_Type_PhyPARTID15 r v)


def _set_MPAMVPM4_EL2_Type_PhyPARTID16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM4_EL2_Type_PhyPARTID16 r v)


def _set_MPAMVPM4_EL2_Type_PhyPARTID17 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM4_EL2_Type_PhyPARTID17 r v)


def _set_MPAMVPM4_EL2_Type_PhyPARTID18 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM4_EL2_Type_PhyPARTID18 r v)


def _set_MPAMVPM4_EL2_Type_PhyPARTID19 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM4_EL2_Type_PhyPARTID19 r v)


def _set_MPAMVPM5_EL2_Type_PhyPARTID20 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM5_EL2_Type_PhyPARTID20 r v)


def _set_MPAMVPM5_EL2_Type_PhyPARTID21 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM5_EL2_Type_PhyPARTID21 r v)


def _set_MPAMVPM5_EL2_Type_PhyPARTID22 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM5_EL2_Type_PhyPARTID22 r v)


def _set_MPAMVPM5_EL2_Type_PhyPARTID23 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM5_EL2_Type_PhyPARTID23 r v)


def _set_MPAMVPM6_EL2_Type_PhyPARTID24 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM6_EL2_Type_PhyPARTID24 r v)


def _set_MPAMVPM6_EL2_Type_PhyPARTID25 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM6_EL2_Type_PhyPARTID25 r v)


def _set_MPAMVPM6_EL2_Type_PhyPARTID26 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM6_EL2_Type_PhyPARTID26 r v)


def _set_MPAMVPM6_EL2_Type_PhyPARTID27 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM6_EL2_Type_PhyPARTID27 r v)


def _set_MPAMVPM7_EL2_Type_PhyPARTID28 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM7_EL2_Type_PhyPARTID28 r v)


def _set_MPAMVPM7_EL2_Type_PhyPARTID29 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM7_EL2_Type_PhyPARTID29 r v)


def _set_MPAMVPM7_EL2_Type_PhyPARTID30 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM7_EL2_Type_PhyPARTID30 r v)


def _set_MPAMVPM7_EL2_Type_PhyPARTID31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPAMVPM7_EL2_Type_PhyPARTID31 r v)


def _set_CLIDR_EL1_Type_Ctype1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ctype1 r v)


def _set_CLIDR_Type_Ctype1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CLIDR_Type_Ctype1 r v)


def _set_CLIDR_EL1_Type_Ctype2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ctype2 r v)


def _set_CLIDR_Type_Ctype2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CLIDR_Type_Ctype2 r v)


def _set_CLIDR_EL1_Type_Ctype3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ctype3 r v)


def _set_CLIDR_Type_Ctype3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CLIDR_Type_Ctype3 r v)


def _set_CLIDR_EL1_Type_Ctype4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ctype4 r v)


def _set_CLIDR_Type_Ctype4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CLIDR_Type_Ctype4 r v)


def _set_CLIDR_EL1_Type_Ctype5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ctype5 r v)


def _set_CLIDR_Type_Ctype5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CLIDR_Type_Ctype5 r v)


def _set_CLIDR_EL1_Type_Ctype6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ctype6 r v)


def _set_CLIDR_Type_Ctype6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CLIDR_Type_Ctype6 r v)


def _set_CLIDR_EL1_Type_Ctype7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ctype7 r v)


def _set_CLIDR_Type_Ctype7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CLIDR_Type_Ctype7 r v)


def _set_CLIDR_EL1_Type_ICB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CLIDR_EL1_Type_ICB r v)


def _set_CLIDR_Type_ICB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CLIDR_Type_ICB r v)


def _set_CLIDR_EL1_Type_LoC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CLIDR_EL1_Type_LoC r v)


def _set_CLIDR_Type_LoC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CLIDR_Type_LoC r v)


def _set_CLIDR_EL1_Type_LoUIS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CLIDR_EL1_Type_LoUIS r v)


def _set_CLIDR_Type_LoUIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CLIDR_Type_LoUIS r v)


def _set_CLIDR_EL1_Type_LoUU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CLIDR_EL1_Type_LoUU r v)


def _set_CLIDR_Type_LoUU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CLIDR_Type_LoUU r v)


def _set_CLIDR_EL1_Type_Ttype1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ttype1 r v)


def _set_CLIDR_EL1_Type_Ttype2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ttype2 r v)


def _set_CLIDR_EL1_Type_Ttype3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ttype3 r v)


def _set_CLIDR_EL1_Type_Ttype4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ttype4 r v)


def _set_CLIDR_EL1_Type_Ttype5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ttype5 r v)


def _set_CLIDR_EL1_Type_Ttype6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ttype6 r v)


def _set_CLIDR_EL1_Type_Ttype7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CLIDR_EL1_Type_Ttype7 r v)


def DecodeSW (regval : (BitVec 64)) (cachetype : CacheType) : SailM (Int × Int × Int) := do
  let linesize ← (( do (undefined_int_at (← occLabel 776) ()) ) : SailM Int )
  let setnum ← (( do (undefined_int_at (← occLabel 777) ()) ) : SailM Int )
  let waynum ← (( do (undefined_int_at (← occLabel 778) ()) ) : SailM Int )
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb regval 3 1))
  let w__0 ← (( do (GetCacheInfo level cachetype) ) : SailM (Int × Int × Int) )
  let (tup__0, tup__1, tup__2) := (w__0 : (Int × Int × Int))
  let setnum : Int := tup__0
  let waynum : Int := tup__1
  let linesize : Int := tup__2
  let waynum : Int := waynum
  let setnum : Int := setnum
  (pure ((setnum, waynum, level)))


/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def BitReverse (data : (BitVec k_N)) : SailM (BitVec k_N) := do
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 779)
      (Sail.BitVec.length data))) ) : SailM (BitVec k_N) )
  let result ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Int := ((Sail.BitVec.length result) -i 1)
    (do
      let mut loop_vars := result
      for i in [loop_i_lower:loop_i_upper:1]i do
        let result := loop_vars
        loop_vars :=
          (BitVec.update result (Sail.Int.toNatChecked ((((Sail.BitVec.length result) -i i) -i 1)))
            (Bit
              (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access data (Sail.Int.toNatChecked (i)))]))))
      (pure loop_vars)) ) : SailM (BitVec k_N) )
  (pure ((Sail.BitVec.castWidth result)))


/-- Type quantifiers: k_N : Nat, k_N > 32 -/
def Poly32Mod2 (data_in : (BitVec k_N)) (poly : (BitVec 32)) : SailM (BitVec 32) := do
  ArmFull.assert ((Sail.BitVec.length data_in) >b 32) "sail-arm/v8_base.sail:12544.18-12544.19"
  let data : (BitVec k_N) := data_in
  let data ← (( do
    let loop_i_lower : Nat := 32
    let loop_i_upper : Nat := (Sail.Int.toNatChecked (((Sail.BitVec.length data_in) -i 1)))
    (do
      let mut loop_vars := data
      for i in [loop_i_upper:loop_i_lower:-1]i do
        let data := loop_vars
        let k_loop_i : Nat := i.toNat
        loop_vars :=
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access data (Sail.Int.toNatChecked (i)))])) == 1#1) : Bool)
          then
            (Sail.BitVec.updateSubrange data (Sail.Int.toNatChecked ((i -i 1))) 0
              (Sail.BitVec.castWidth ((Sail.BitVec.castWidth (m := k_loop_i) (Sail.BitVec.extractLsb
                  data (Sail.Int.toNatChecked ((i -i 1))) 0)) ^^^ (Sail.BitVec.castWidth (poly +++ (Zeros
                    (n := (Sail.Int.toNatChecked ((i -i 32))))))))))
          else data
      (pure loop_vars)) ) : SailM (BitVec k_N) )
  (pure ((Sail.BitVec.extractLsb data 31 0)))


/-- Type quantifiers: k_N : Nat, shift : Int, k_N ≥ 0 -/
def ROL (x : (BitVec k_N)) (shift : Int) : SailM (BitVec k_N) := do
  ArmFull.assert ((shift ≥b 0) && (shift ≤b (Sail.BitVec.length x))) "sail-arm/v8_base.sail:12606.35-12606.36"
  (pure (if ((shift == 0) : Bool)
    then (Sail.BitVec.castWidth x)
    else (Sail.BitVec.castWidth (ROR x (Sail.Int.toNatChecked (((Sail.BitVec.length x) -i shift)))))))


def AESSubBytes (op : (BitVec 128)) : SailM (BitVec 128) := do
  let GF2 : (BitVec 2048) :=
    (((((((((((((((0x16BB54B00F2D99416842E6BF0D89A18C#128 +++ 0xDF2855CEE9871E9B948ED9691198F8E1#128) +++ 0x9E1DC186B95735610EF6034866B53E70#128) +++ 0x8A8BBD4B1F74DDE8C6B4A61C2E2578BA#128) +++ 0x08AE7A65EAF4566CA94ED58D6D37C8E7#128) +++ 0x79E4959162ACD3C25C2406490A3A32E0#128) +++ 0xDB0B5EDE14B8EE4688902A22DC4F8160#128) +++ 0x73195D643D7EA7C41744975FEC130CCD#128) +++ 0xD2F3FF1021DAB6BCF5389D928F40A351#128) +++ 0xA89F3C507F02F94585334D43FBAAEFD0#128) +++ 0xCF584C4A39BECB6A5BB1FC20ED00D153#128) +++ 0x842FE329B3D63B52A05A6E1B1A2C8309#128) +++ 0x75B227EBE28012079A059618C323C704#128) +++ 0x1531D871F1E5A534CCF73F362693FDB7#128) +++ 0xC072A49CAFA2D4ADF04759FA7DC982CA#128) +++ 0x76ABD7FE2B670130C56F6BF27B777C63#128)
  let out ← (( do (undefined_bitvector_at (← occLabel 780) 128) ) : SailM (BitVec 128) )
  let out ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := 15
    (do
      let mut loop_vars := out
      for i in [loop_i_lower:loop_i_upper:1]i do
        let out := loop_vars
        loop_vars :=
          (set_slice 8 out (Sail.Int.toNatChecked ((i *i 8)))
            (BitVec.slice GF2
              (Sail.Int.toNatChecked (((BitVec.toNat
                  (BitVec.slice op (Sail.Int.toNatChecked ((i *i 8))) 8)) *i 8))) 8))
      (pure loop_vars)) ) : SailM (BitVec 128) )
  (pure (out))


def AESInvSubBytes (op : (BitVec 128)) : SailM (BitVec 128) := do
  let GF2_inv : (BitVec 2048) :=
    (((((((((((((((0x7D0C2155631469E126D677BA7E042B17#128 +++ 0x619953833CBBEBC8B0F52AAE4D3BE0A0#128) +++ 0xEF9CC9939F7AE52D0D4AB519A97F5160#128) +++ 0x5FEC8027591012B131C7078833A8DD1F#128) +++ 0xF45ACD78FEC0DB9A2079D2C64B3E56FC#128) +++ 0x1BBE18AA0E62B76F89C5291D711AF147#128) +++ 0x6EDF751CE837F9E28535ADE72274AC96#128) +++ 0x73E6B4F0CECFF297EADC674F4111913A#128) +++ 0x6B8A130103BDAFC1020F3FCA8F1E2CD0#128) +++ 0x0645B3B80558E4F70AD3BC8C00ABD890#128) +++ 0x849D8DA75746155EDAB9EDFD5048706C#128) +++ 0x92B6655DCC5CA4D41698688664F6F872#128) +++ 0x25D18B6D49A25B76B224D92866A12E08#128) +++ 0x4EC3FA420B954CEE3D23C2A632947B54#128) +++ 0xCBE9DEC444438E3487FF2F9B8239E37C#128) +++ 0xFBD7F3819EA340BF38A53630D56A0952#128)
  let out ← (( do (undefined_bitvector_at (← occLabel 781) 128) ) : SailM (BitVec 128) )
  let out ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := 15
    (do
      let mut loop_vars := out
      for i in [loop_i_lower:loop_i_upper:1]i do
        let out := loop_vars
        loop_vars :=
          (set_slice 8 out (Sail.Int.toNatChecked ((i *i 8)))
            (BitVec.slice GF2_inv
              (Sail.Int.toNatChecked (((BitVec.toNat
                  (BitVec.slice op (Sail.Int.toNatChecked ((i *i 8))) 8)) *i 8))) 8))
      (pure loop_vars)) ) : SailM (BitVec 128) )
  (pure (out))


def AESMixColumns (op : (BitVec 128)) : SailM (BitVec 128) := do
  let in0 : (BitVec 32) :=
    ((((BitVec.slice op 96 8) +++ (BitVec.slice op 64 8)) +++ (BitVec.slice op 32 8)) +++ (BitVec.slice
        op 0 8))
  let in1 : (BitVec 32) :=
    ((((BitVec.slice op 104 8) +++ (BitVec.slice op 72 8)) +++ (BitVec.slice op 40 8)) +++ (BitVec.slice
        op 8 8))
  let in2 : (BitVec 32) :=
    ((((BitVec.slice op 112 8) +++ (BitVec.slice op 80 8)) +++ (BitVec.slice op 48 8)) +++ (BitVec.slice
        op 16 8))
  let in3 : (BitVec 32) :=
    ((((BitVec.slice op 120 8) +++ (BitVec.slice op 88 8)) +++ (BitVec.slice op 56 8)) +++ (BitVec.slice
        op 24 8))
  let out0 ← (( do (undefined_bitvector_at (← occLabel 782) 32) ) : SailM (BitVec 32) )
  let out1 ← (( do (undefined_bitvector_at (← occLabel 783) 32) ) : SailM (BitVec 32) )
  let out2 ← (( do (undefined_bitvector_at (← occLabel 784) 32) ) : SailM (BitVec 32) )
  let out3 ← (( do (undefined_bitvector_at (← occLabel 785) 32) ) : SailM (BitVec 32) )
  let (out0, out1, out2, out3) ← (( do
    let loop_c_lower : Nat := 0
    let loop_c_upper : Nat := 3
    (do
      let mut loop_vars := (out0, out1, out2, out3)
      for c in [loop_c_lower:loop_c_upper:1]i do
        let (out0, out1, out2, out3) := loop_vars
        loop_vars :=
          let out0 : (BitVec 32) :=
            (set_slice 8 out0 (Sail.Int.toNatChecked ((c *i 8)))
              ((Sail.BitVec.castWidth (m := 8) (((FFmul02
                      (BitVec.slice in0 (Sail.Int.toNatChecked ((c *i 8))) 8)) ^^^ (FFmul03
                      (BitVec.slice in1 (Sail.Int.toNatChecked ((c *i 8))) 8))) ^^^ (Sail.BitVec.castWidth (m := 8) (BitVec.slice
                    in2 (Sail.Int.toNatChecked ((c *i 8))) 8)))) ^^^ (Sail.BitVec.castWidth (m := 8) (BitVec.slice
                  in3 (Sail.Int.toNatChecked ((c *i 8))) 8))))
          let out1 : (BitVec 32) :=
            (set_slice 8 out1 (Sail.Int.toNatChecked ((c *i 8)))
              ((Sail.BitVec.castWidth (m := 8) (((FFmul02
                      (BitVec.slice in1 (Sail.Int.toNatChecked ((c *i 8))) 8)) ^^^ (FFmul03
                      (BitVec.slice in2 (Sail.Int.toNatChecked ((c *i 8))) 8))) ^^^ (Sail.BitVec.castWidth (m := 8) (BitVec.slice
                    in3 (Sail.Int.toNatChecked ((c *i 8))) 8)))) ^^^ (Sail.BitVec.castWidth (m := 8) (BitVec.slice
                  in0 (Sail.Int.toNatChecked ((c *i 8))) 8))))
          let out2 : (BitVec 32) :=
            (set_slice 8 out2 (Sail.Int.toNatChecked ((c *i 8)))
              ((Sail.BitVec.castWidth (m := 8) (((FFmul02
                      (BitVec.slice in2 (Sail.Int.toNatChecked ((c *i 8))) 8)) ^^^ (FFmul03
                      (BitVec.slice in3 (Sail.Int.toNatChecked ((c *i 8))) 8))) ^^^ (Sail.BitVec.castWidth (m := 8) (BitVec.slice
                    in0 (Sail.Int.toNatChecked ((c *i 8))) 8)))) ^^^ (Sail.BitVec.castWidth (m := 8) (BitVec.slice
                  in1 (Sail.Int.toNatChecked ((c *i 8))) 8))))
          let out3 : (BitVec 32) :=
            (set_slice 8 out3 (Sail.Int.toNatChecked ((c *i 8)))
              ((Sail.BitVec.castWidth (m := 8) (((FFmul02
                      (BitVec.slice in3 (Sail.Int.toNatChecked ((c *i 8))) 8)) ^^^ (FFmul03
                      (BitVec.slice in0 (Sail.Int.toNatChecked ((c *i 8))) 8))) ^^^ (Sail.BitVec.castWidth (m := 8) (BitVec.slice
                    in1 (Sail.Int.toNatChecked ((c *i 8))) 8)))) ^^^ (Sail.BitVec.castWidth (m := 8) (BitVec.slice
                  in2 (Sail.Int.toNatChecked ((c *i 8))) 8))))
          (out0, out1, out2, out3)
      (pure loop_vars)) ) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 32) × (BitVec 32)) )
  (pure (((((((((((((((((BitVec.slice out3 (Sail.Int.toNatChecked ((3 *i 8))) 8) +++ (BitVec.slice
                                    out2 (Sail.Int.toNatChecked ((3 *i 8))) 8)) +++ (BitVec.slice
                                  out1 (Sail.Int.toNatChecked ((3 *i 8))) 8)) +++ (BitVec.slice out0
                                (Sail.Int.toNatChecked ((3 *i 8))) 8)) +++ (BitVec.slice out3
                              (Sail.Int.toNatChecked ((2 *i 8))) 8)) +++ (BitVec.slice out2
                            (Sail.Int.toNatChecked ((2 *i 8))) 8)) +++ (BitVec.slice out1
                          (Sail.Int.toNatChecked ((2 *i 8))) 8)) +++ (BitVec.slice out0
                        (Sail.Int.toNatChecked ((2 *i 8))) 8)) +++ (BitVec.slice out3
                      (Sail.Int.toNatChecked ((1 *i 8))) 8)) +++ (BitVec.slice out2
                    (Sail.Int.toNatChecked ((1 *i 8))) 8)) +++ (BitVec.slice out1
                  (Sail.Int.toNatChecked ((1 *i 8))) 8)) +++ (BitVec.slice out0
                (Sail.Int.toNatChecked ((1 *i 8))) 8)) +++ (BitVec.slice out3
              (Sail.Int.toNatChecked ((0 *i 8))) 8)) +++ (BitVec.slice out2
            (Sail.Int.toNatChecked ((0 *i 8))) 8)) +++ (BitVec.slice out1
          (Sail.Int.toNatChecked ((0 *i 8))) 8)) +++ (BitVec.slice out0
        (Sail.Int.toNatChecked ((0 *i 8))) 8))))


def AESInvMixColumns (op : (BitVec 128)) : SailM (BitVec 128) := do
  let in0 : (BitVec 32) :=
    ((((BitVec.slice op 96 8) +++ (BitVec.slice op 64 8)) +++ (BitVec.slice op 32 8)) +++ (BitVec.slice
        op 0 8))
  let in1 : (BitVec 32) :=
    ((((BitVec.slice op 104 8) +++ (BitVec.slice op 72 8)) +++ (BitVec.slice op 40 8)) +++ (BitVec.slice
        op 8 8))
  let in2 : (BitVec 32) :=
    ((((BitVec.slice op 112 8) +++ (BitVec.slice op 80 8)) +++ (BitVec.slice op 48 8)) +++ (BitVec.slice
        op 16 8))
  let in3 : (BitVec 32) :=
    ((((BitVec.slice op 120 8) +++ (BitVec.slice op 88 8)) +++ (BitVec.slice op 56 8)) +++ (BitVec.slice
        op 24 8))
  let out0 ← (( do (undefined_bitvector_at (← occLabel 786) 32) ) : SailM (BitVec 32) )
  let out1 ← (( do (undefined_bitvector_at (← occLabel 787) 32) ) : SailM (BitVec 32) )
  let out2 ← (( do (undefined_bitvector_at (← occLabel 788) 32) ) : SailM (BitVec 32) )
  let out3 ← (( do (undefined_bitvector_at (← occLabel 789) 32) ) : SailM (BitVec 32) )
  let (out0, out1, out2, out3) ← (( do
    let loop_c_lower : Nat := 0
    let loop_c_upper : Nat := 3
    (do
      let mut loop_vars := (out0, out1, out2, out3)
      for c in [loop_c_lower:loop_c_upper:1]i do
        let (out0, out1, out2, out3) := loop_vars
        loop_vars :=
          let out0 : (BitVec 32) :=
            (set_slice 8 out0 (Sail.Int.toNatChecked ((c *i 8)))
              ((((FFmul0E (BitVec.slice in0 (Sail.Int.toNatChecked ((c *i 8))) 8)) ^^^ (FFmul0B
                      (BitVec.slice in1 (Sail.Int.toNatChecked ((c *i 8))) 8))) ^^^ (FFmul0D
                    (BitVec.slice in2 (Sail.Int.toNatChecked ((c *i 8))) 8))) ^^^ (FFmul09
                  (BitVec.slice in3 (Sail.Int.toNatChecked ((c *i 8))) 8))))
          let out1 : (BitVec 32) :=
            (set_slice 8 out1 (Sail.Int.toNatChecked ((c *i 8)))
              ((((FFmul09 (BitVec.slice in0 (Sail.Int.toNatChecked ((c *i 8))) 8)) ^^^ (FFmul0E
                      (BitVec.slice in1 (Sail.Int.toNatChecked ((c *i 8))) 8))) ^^^ (FFmul0B
                    (BitVec.slice in2 (Sail.Int.toNatChecked ((c *i 8))) 8))) ^^^ (FFmul0D
                  (BitVec.slice in3 (Sail.Int.toNatChecked ((c *i 8))) 8))))
          let out2 : (BitVec 32) :=
            (set_slice 8 out2 (Sail.Int.toNatChecked ((c *i 8)))
              ((((FFmul0D (BitVec.slice in0 (Sail.Int.toNatChecked ((c *i 8))) 8)) ^^^ (FFmul09
                      (BitVec.slice in1 (Sail.Int.toNatChecked ((c *i 8))) 8))) ^^^ (FFmul0E
                    (BitVec.slice in2 (Sail.Int.toNatChecked ((c *i 8))) 8))) ^^^ (FFmul0B
                  (BitVec.slice in3 (Sail.Int.toNatChecked ((c *i 8))) 8))))
          let out3 : (BitVec 32) :=
            (set_slice 8 out3 (Sail.Int.toNatChecked ((c *i 8)))
              ((((FFmul0B (BitVec.slice in0 (Sail.Int.toNatChecked ((c *i 8))) 8)) ^^^ (FFmul0D
                      (BitVec.slice in1 (Sail.Int.toNatChecked ((c *i 8))) 8))) ^^^ (FFmul09
                    (BitVec.slice in2 (Sail.Int.toNatChecked ((c *i 8))) 8))) ^^^ (FFmul0E
                  (BitVec.slice in3 (Sail.Int.toNatChecked ((c *i 8))) 8))))
          (out0, out1, out2, out3)
      (pure loop_vars)) ) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 32) × (BitVec 32)) )
  (pure (((((((((((((((((BitVec.slice out3 (Sail.Int.toNatChecked ((3 *i 8))) 8) +++ (BitVec.slice
                                    out2 (Sail.Int.toNatChecked ((3 *i 8))) 8)) +++ (BitVec.slice
                                  out1 (Sail.Int.toNatChecked ((3 *i 8))) 8)) +++ (BitVec.slice out0
                                (Sail.Int.toNatChecked ((3 *i 8))) 8)) +++ (BitVec.slice out3
                              (Sail.Int.toNatChecked ((2 *i 8))) 8)) +++ (BitVec.slice out2
                            (Sail.Int.toNatChecked ((2 *i 8))) 8)) +++ (BitVec.slice out1
                          (Sail.Int.toNatChecked ((2 *i 8))) 8)) +++ (BitVec.slice out0
                        (Sail.Int.toNatChecked ((2 *i 8))) 8)) +++ (BitVec.slice out3
                      (Sail.Int.toNatChecked ((1 *i 8))) 8)) +++ (BitVec.slice out2
                    (Sail.Int.toNatChecked ((1 *i 8))) 8)) +++ (BitVec.slice out1
                  (Sail.Int.toNatChecked ((1 *i 8))) 8)) +++ (BitVec.slice out0
                (Sail.Int.toNatChecked ((1 *i 8))) 8)) +++ (BitVec.slice out3
              (Sail.Int.toNatChecked ((0 *i 8))) 8)) +++ (BitVec.slice out2
            (Sail.Int.toNatChecked ((0 *i 8))) 8)) +++ (BitVec.slice out1
          (Sail.Int.toNatChecked ((0 *i 8))) 8)) +++ (BitVec.slice out0
        (Sail.Int.toNatChecked ((0 *i 8))) 8))))


end ArmFull.Functions
