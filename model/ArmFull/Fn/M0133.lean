import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0036
import ArmFull.Fn.M0056
import ArmFull.Fn.M0057
import ArmFull.Fn.M0058
import ArmFull.Fn.M0075
import ArmFull.Fn.M0076

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

def _set_ID_ISAR5_Type_SEVL (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_ISAR5_Type_SEVL r v)


def _set_ID_ISAR5_EL1_Type_VCMA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_ISAR5_EL1_Type_VCMA r v)


def _set_ID_ISAR5_Type_VCMA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_ISAR5_Type_VCMA r v)


def _set_ICH_HCR_EL2_Type_DVIM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_DVIM r v)


def _set_ICH_VTR_EL2_Type_DVIM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_VTR_EL2_Type_DVIM r v)


def _set_ICH_HCR_EL2_Type_EOIcount (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_EOIcount r v)


def _set_ICH_HCR_Type_EOIcount (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_HCR_Type_EOIcount r v)


def _set_ICH_HCR_EL2_Type_En (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_En r v)


def _set_GICH_HCR_Type_En (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_HCR_Type_En r v)


def _set_ICH_HCR_Type_En (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_HCR_Type_En r v)


def _set_ICH_HCR_EL2_Type_LRENPIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_LRENPIE r v)


def _set_GICH_HCR_Type_LRENPIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_HCR_Type_LRENPIE r v)


def _set_ICH_HCR_Type_LRENPIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_HCR_Type_LRENPIE r v)


def _set_ICH_HCR_EL2_Type_NPIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_NPIE r v)


def _set_GICH_HCR_Type_NPIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_HCR_Type_NPIE r v)


def _set_ICH_HCR_Type_NPIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_HCR_Type_NPIE r v)


def _set_ICH_HCR_EL2_Type_TALL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_TALL0 r v)


def _set_ICH_HCR_Type_TALL0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_HCR_Type_TALL0 r v)


def _set_ICH_HCR_EL2_Type_TALL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_TALL1 r v)


def _set_ICH_HCR_Type_TALL1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_HCR_Type_TALL1 r v)


def _set_ICH_HCR_EL2_Type_TDIR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_TDIR r v)


def _set_ICH_HCR_Type_TDIR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_HCR_Type_TDIR r v)


def _set_ICH_HCR_EL2_Type_TSEI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_TSEI r v)


def _set_ICH_HCR_Type_TSEI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_HCR_Type_TSEI r v)


def _set_ICH_HCR_EL2_Type_UIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_UIE r v)


def _set_GICH_HCR_Type_UIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_HCR_Type_UIE r v)


def _set_ICH_HCR_Type_UIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_HCR_Type_UIE r v)


def _set_ICH_HCR_EL2_Type_VGrp0DIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_VGrp0DIE r v)


def _set_GICH_HCR_Type_VGrp0DIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_HCR_Type_VGrp0DIE r v)


def _set_ICH_HCR_Type_VGrp0DIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_HCR_Type_VGrp0DIE r v)


def _set_ICH_HCR_EL2_Type_VGrp0EIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_VGrp0EIE r v)


def _set_GICH_HCR_Type_VGrp0EIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_HCR_Type_VGrp0EIE r v)


def _set_ICH_HCR_Type_VGrp0EIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_HCR_Type_VGrp0EIE r v)


def _set_ICH_HCR_EL2_Type_VGrp1DIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_VGrp1DIE r v)


def _set_GICH_HCR_Type_VGrp1DIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_HCR_Type_VGrp1DIE r v)


def _set_ICH_HCR_Type_VGrp1DIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_HCR_Type_VGrp1DIE r v)


def _set_ICH_HCR_EL2_Type_VGrp1EIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_VGrp1EIE r v)


def _set_GICH_HCR_Type_VGrp1EIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_HCR_Type_VGrp1EIE r v)


def _set_ICH_HCR_Type_VGrp1EIE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_HCR_Type_VGrp1EIE r v)


def _set_ICH_HCR_EL2_Type_vSGIEOICount (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_HCR_EL2_Type_vSGIEOICount r v)


def _set_ICH_HCR_Type_vSGIEOICount (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_HCR_Type_vSGIEOICount r v)


def _set_ID_AA64MMFR0_EL1_Type_ASIDBits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_ASIDBits r v)


def _set_ID_AA64MMFR0_EL1_Type_BigEnd (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_BigEnd r v)


def _set_ID_AA64MMFR0_EL1_Type_BigEndEL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_BigEndEL0 r v)


def _set_ID_AA64MMFR0_EL1_Type_ExS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_ExS r v)


def _set_ID_AA64MMFR0_EL1_Type_FGT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_FGT r v)


def _set_ID_AA64MMFR0_EL1_Type_PARange (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_PARange r v)


def _set_ID_AA64MMFR0_EL1_Type_SNSMem (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_SNSMem r v)


def _set_ID_AA64MMFR0_EL1_Type_TGran16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_TGran16 r v)


def _set_ID_AA64MMFR0_EL1_Type_TGran16_2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_TGran16_2 r v)


def _set_ID_AA64MMFR0_EL1_Type_TGran4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_TGran4 r v)


def _set_ID_AA64MMFR0_EL1_Type_TGran4_2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_TGran4_2 r v)


def _set_ID_AA64MMFR0_EL1_Type_TGran64 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_TGran64 r v)


def _set_ID_AA64MMFR0_EL1_Type_TGran64_2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_TGran64_2 r v)


def _set_HDFGRTR2_EL2_Type_nPMSSDATA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nPMSSDATA r v)


def _set_HDFGRTR2_EL2_Type_nSPMDEVAFF_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nSPMDEVAFF_EL1 r v)


def _set_HDFGRTR2_EL2_Type_nSPMID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nSPMID r v)


def _set_VMPIDR_EL2_Type_Aff0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VMPIDR_EL2_Type_Aff0 r v)


def _set_MPIDR_EL1_Type_Aff0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPIDR_EL1_Type_Aff0 r v)


def _set_MPIDR_Type_Aff0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MPIDR_Type_Aff0 r v)


def _set_VMPIDR_Type_Aff0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_VMPIDR_Type_Aff0 r v)


def _set_ID_AA64MMFR3_EL1_Type_ADERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_ADERR r v)


def _set_ID_AA64MMFR3_EL1_Type_ANERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_ANERR r v)


def _set_ID_AA64MMFR3_EL1_Type_D128_2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_D128_2 r v)


def _set_ID_AA64MMFR3_EL1_Type_MEC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_MEC r v)


def _set_ID_AA64MMFR3_EL1_Type_S1PIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_S1PIE r v)


def _set_ID_AA64MMFR3_EL1_Type_S1POE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_S1POE r v)


def _set_ID_AA64MMFR3_EL1_Type_SCTLRX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_SCTLRX r v)


def _set_ID_AA64MMFR3_EL1_Type_SDERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_SDERR r v)


def _set_ID_AA64MMFR3_EL1_Type_SNERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_SNERR r v)


def _set_ID_AA64MMFR3_EL1_Type_Spec_FPACC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_Spec_FPACC r v)


def _set_ID_AA64MMFR3_EL1_Type_TCRX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_TCRX r v)


def _set_ICH_VTR_EL2_Type_ListRegs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_VTR_EL2_Type_ListRegs r v)


def _set_GICH_VTR_Type_ListRegs (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_VTR_Type_ListRegs r v)


def _set_ICH_VTR_Type_ListRegs (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_VTR_Type_ListRegs r v)


def _set_ICH_VTR_EL2_Type_PREbits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_VTR_EL2_Type_PREbits r v)


def _set_GICH_VTR_Type_PREbits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_VTR_Type_PREbits r v)


def _set_ICH_VTR_Type_PREbits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_VTR_Type_PREbits r v)


def _set_ICH_VTR_EL2_Type_TDS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_VTR_EL2_Type_TDS r v)


def _set_ICH_VTR_Type_TDS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_VTR_Type_TDS r v)


def _set_ICH_VTR_EL2_Type_nV4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_VTR_EL2_Type_nV4 r v)


def _set_ICH_VTR_Type_nV4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_VTR_Type_nV4 r v)


def _set_ID_PFR1_EL1_Type_GenTimer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_PFR1_EL1_Type_GenTimer r v)


def _set_ID_PFR1_Type_GenTimer (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_PFR1_Type_GenTimer r v)


def _set_ID_PFR1_EL1_Type_MProgMod (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_PFR1_EL1_Type_MProgMod r v)


def _set_ID_PFR1_Type_MProgMod (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_PFR1_Type_MProgMod r v)


def _set_ID_PFR1_EL1_Type_ProgMod (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_PFR1_EL1_Type_ProgMod r v)


def _set_ID_PFR1_Type_ProgMod (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_PFR1_Type_ProgMod r v)


def _set_ID_PFR1_EL1_Type_Sec_frac (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_PFR1_EL1_Type_Sec_frac r v)


def _set_ID_PFR1_Type_Sec_frac (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_PFR1_Type_Sec_frac r v)


def _set_ID_PFR1_EL1_Type_Security (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_PFR1_EL1_Type_Security r v)


def _set_ID_PFR1_Type_Security (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_PFR1_Type_Security r v)


def _set_ID_PFR1_EL1_Type_Virt_frac (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_PFR1_EL1_Type_Virt_frac r v)


def _set_ID_PFR1_Type_Virt_frac (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_PFR1_Type_Virt_frac r v)


def _set_ID_PFR1_EL1_Type_Virtualization (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_PFR1_EL1_Type_Virtualization r v)


def _set_ID_PFR1_Type_Virtualization (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_PFR1_Type_Virtualization r v)


def __set_MDSELR_EL1 (value_name : (BitVec 64)) : SailM Unit := do
  let r : MDSELR_EL1_Type := value_name
  let w__0 ← (( do readReg MDSELR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSELR_EL1 (Sail.BitVec.updateSubrange w__0 3 0 (BitVec.slice r 0 4))
  let w__1 ← (( do readReg MDSELR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSELR_EL1 (Sail.BitVec.updateSubrange w__1 63 6 (BitVec.slice r 6 58))
  let w__4 ← (( do
    if ((← do
         let w__2 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
         (pure (((w__2 ≤b 16) : Bool)))) : Bool)
    then
      (do
        let w__3 ← (( do readReg NUM_WATCHPOINTS ) : SailM Int )
        (pure (((w__3 ≤b 16) : Bool))))
    else (pure false) ) : SailM Bool )
  if ((! w__4) : Bool)
  then
    (do
      let w__5 ← (( do readReg MDSELR_EL1 ) : SailM (BitVec 64) )
      writeReg MDSELR_EL1 (Sail.BitVec.updateSubrange w__5 5 4 (_get_MDSELR_EL1_Type_BANK r)))
  else (pure (()))


def _set_RNDRRS_Type_RNDRRS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_RNDRRS_Type_RNDRRS r v)


def _set_LORN_EL1_Type_Num (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_LORN_EL1_Type_Num r v)


def _set_CCSIDR_EL1_Type_Associativity (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 21)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CCSIDR_EL1_Type_Associativity r v)


def _set_CCSIDR_Type_Associativity (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 21)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CCSIDR_Type_Associativity r v)


def _set_CCSIDR_EL1_Type_LineSize (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CCSIDR_EL1_Type_LineSize r v)


def _set_CCSIDR_Type_LineSize (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CCSIDR_Type_LineSize r v)


def _set_HFGRTR_EL2_Type_AIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_AIDR_EL1 r v)


def _set_HFGRTR_EL2_Type_CCSIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_CCSIDR_EL1 r v)


def _set_HFGRTR_EL2_Type_CLIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_CLIDR_EL1 r v)


def _set_HFGRTR_EL2_Type_CTR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_CTR_EL0 r v)


def _set_HFGRTR_EL2_Type_DCZID_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_DCZID_EL0 r v)


def _set_HFGRTR_EL2_Type_ERRIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_ERRIDR_EL1 r v)


def _set_HFGRTR_EL2_Type_ERXFR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_ERXFR_EL1 r v)


def _set_HFGRTR_EL2_Type_ERXPFGF_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_ERXPFGF_EL1 r v)


def _set_HFGRTR_EL2_Type_ISR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_ISR_EL1 r v)


def _set_HFGRTR_EL2_Type_LORID_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_LORID_EL1 r v)


def _set_HFGRTR_EL2_Type_MIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_MIDR_EL1 r v)


def _set_HFGRTR_EL2_Type_MPIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_MPIDR_EL1 r v)


def _set_HFGRTR_EL2_Type_REVIDR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR_EL2_Type_REVIDR_EL1 r v)


def _set_ID_DFR0_EL1_Type_CopDbg (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_DFR0_EL1_Type_CopDbg r v)


def _set_ID_DFR0_Type_CopDbg (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_DFR0_Type_CopDbg r v)


def _set_ID_DFR0_EL1_Type_CopSDbg (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_DFR0_EL1_Type_CopSDbg r v)


def _set_ID_DFR0_Type_CopSDbg (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_DFR0_Type_CopSDbg r v)


def _set_ID_DFR0_EL1_Type_CopTrc (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_DFR0_EL1_Type_CopTrc r v)


def _set_ID_DFR0_Type_CopTrc (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_DFR0_Type_CopTrc r v)


def _set_ID_DFR0_EL1_Type_MMapDbg (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_DFR0_EL1_Type_MMapDbg r v)


def _set_ID_DFR0_Type_MMapDbg (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_DFR0_Type_MMapDbg r v)


def _set_ID_DFR0_EL1_Type_MMapTrc (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_DFR0_EL1_Type_MMapTrc r v)


def _set_ID_DFR0_Type_MMapTrc (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_DFR0_Type_MMapTrc r v)


def _set_ID_DFR0_EL1_Type_MProfDbg (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_DFR0_EL1_Type_MProfDbg r v)


def _set_ID_DFR0_Type_MProfDbg (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_DFR0_Type_MProfDbg r v)


def _set_ID_DFR0_EL1_Type_PerfMon (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_DFR0_EL1_Type_PerfMon r v)


def _set_ID_DFR0_Type_PerfMon (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_DFR0_Type_PerfMon r v)


def _set_PMXEVCNTR_EL0_Type_PMEVCNTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMXEVCNTR_EL0_Type_PMEVCNTR r v)


def _set_MVFR2_EL1_Type_FPMisc (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MVFR2_EL1_Type_FPMisc r v)


def _set_MVFR2_Type_FPMisc (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MVFR2_Type_FPMisc r v)


def _set_MVFR2_EL1_Type_SIMDMisc (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MVFR2_EL1_Type_SIMDMisc r v)


def _set_MVFR2_Type_SIMDMisc (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MVFR2_Type_SIMDMisc r v)


def _set_DBGAUTHSTATUS_EL1_Type_NSID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGAUTHSTATUS_EL1_Type_NSID r v)


def _set_CTIAUTHSTATUS_Type_NSID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTIAUTHSTATUS_Type_NSID r v)


def _set_DBGAUTHSTATUS_Type_NSID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGAUTHSTATUS_Type_NSID r v)


def _set_PMAUTHSTATUS_Type_NSID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMAUTHSTATUS_Type_NSID r v)


def _set_DBGAUTHSTATUS_EL1_Type_NSNID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGAUTHSTATUS_EL1_Type_NSNID r v)


def _set_CTIAUTHSTATUS_Type_NSNID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTIAUTHSTATUS_Type_NSNID r v)


def _set_DBGAUTHSTATUS_Type_NSNID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGAUTHSTATUS_Type_NSNID r v)


def _set_PMAUTHSTATUS_Type_NSNID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMAUTHSTATUS_Type_NSNID r v)


def _set_DBGAUTHSTATUS_EL1_Type_RLID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGAUTHSTATUS_EL1_Type_RLID r v)


def _set_PMAUTHSTATUS_Type_RLID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMAUTHSTATUS_Type_RLID r v)


def _set_DBGAUTHSTATUS_EL1_Type_RLNID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGAUTHSTATUS_EL1_Type_RLNID r v)


end ArmFull.Functions
