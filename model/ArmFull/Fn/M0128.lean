import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0056
import ArmFull.Fn.M0057
import ArmFull.Fn.M0058
import ArmFull.Fn.M0068
import ArmFull.Fn.M0069

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

def _set_GICH_EISR_Type_Status5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_EISR_Type_Status5 r v)


def _set_GICH_ELRSR_Type_Status5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status5 r v)


def _set_ICH_EISR_Type_Status5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_EISR_Type_Status5 r v)


def _set_ICH_ELRSR_EL2_Type_Status5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status5 r v)


def _set_ICH_ELRSR_Type_Status5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status5 r v)


def _set_ICH_EISR_EL2_Type_Status6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status6 r v)


def _set_GICH_EISR_Type_Status6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_EISR_Type_Status6 r v)


def _set_GICH_ELRSR_Type_Status6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status6 r v)


def _set_ICH_EISR_Type_Status6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_EISR_Type_Status6 r v)


def _set_ICH_ELRSR_EL2_Type_Status6 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status6 r v)


def _set_ICH_ELRSR_Type_Status6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status6 r v)


def _set_ICH_EISR_EL2_Type_Status7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status7 r v)


def _set_GICH_EISR_Type_Status7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_EISR_Type_Status7 r v)


def _set_GICH_ELRSR_Type_Status7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status7 r v)


def _set_ICH_EISR_Type_Status7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_EISR_Type_Status7 r v)


def _set_ICH_ELRSR_EL2_Type_Status7 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status7 r v)


def _set_ICH_ELRSR_Type_Status7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status7 r v)


def _set_ICH_EISR_EL2_Type_Status8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status8 r v)


def _set_GICH_EISR_Type_Status8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_EISR_Type_Status8 r v)


def _set_GICH_ELRSR_Type_Status8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status8 r v)


def _set_ICH_EISR_Type_Status8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_EISR_Type_Status8 r v)


def _set_ICH_ELRSR_EL2_Type_Status8 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status8 r v)


def _set_ICH_ELRSR_Type_Status8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status8 r v)


def _set_ICH_EISR_EL2_Type_Status9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status9 r v)


def _set_GICH_EISR_Type_Status9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_EISR_Type_Status9 r v)


def _set_GICH_ELRSR_Type_Status9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status9 r v)


def _set_ICH_EISR_Type_Status9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_EISR_Type_Status9 r v)


def _set_ICH_ELRSR_EL2_Type_Status9 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status9 r v)


def _set_ICH_ELRSR_Type_Status9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status9 r v)


def _set_MIDR_EL1_Type_Architecture (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MIDR_EL1_Type_Architecture r v)


def _set_MIDR_Type_Architecture (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MIDR_Type_Architecture r v)


def _set_VPIDR_EL2_Type_Architecture (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VPIDR_EL2_Type_Architecture r v)


def _set_VPIDR_Type_Architecture (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_VPIDR_Type_Architecture r v)


def _set_MIDR_EL1_Type_Implementer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MIDR_EL1_Type_Implementer r v)


def _set_AMIIDR_Type_Implementer (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 12)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMIIDR_Type_Implementer r v)


def _set_FPSID_Type_Implementer (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSID_Type_Implementer r v)


def _set_GICD_IIDR_Type_Implementer (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 12)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_IIDR_Type_Implementer r v)


def _set_GICM_IIDR_Type_Implementer (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 12)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICM_IIDR_Type_Implementer r v)


def _set_GICR_IIDR_Type_Implementer (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 12)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_IIDR_Type_Implementer r v)


def _set_GITS_IIDR_Type_Implementer (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 12)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GITS_IIDR_Type_Implementer r v)


def _set_MIDR_Type_Implementer (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MIDR_Type_Implementer r v)


def _set_SMIDR_EL1_Type_Implementer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SMIDR_EL1_Type_Implementer r v)


def _set_VPIDR_EL2_Type_Implementer (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VPIDR_EL2_Type_Implementer r v)


def _set_VPIDR_Type_Implementer (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_VPIDR_Type_Implementer r v)


def _set_MIDR_EL1_Type_PartNum (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 12)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MIDR_EL1_Type_PartNum r v)


def _set_FPSID_Type_PartNum (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSID_Type_PartNum r v)


def _set_MIDR_Type_PartNum (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 12)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MIDR_Type_PartNum r v)


def _set_VPIDR_EL2_Type_PartNum (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 12)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VPIDR_EL2_Type_PartNum r v)


def _set_VPIDR_Type_PartNum (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 12)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_VPIDR_Type_PartNum r v)


def _set_MIDR_EL1_Type_Revision (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MIDR_EL1_Type_Revision r v)


def _set_AMIIDR_Type_Revision (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMIIDR_Type_Revision r v)


def _set_FPSID_Type_Revision (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSID_Type_Revision r v)


def _set_GICD_IIDR_Type_Revision (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_IIDR_Type_Revision r v)


def _set_GICM_IIDR_Type_Revision (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICM_IIDR_Type_Revision r v)


def _set_GICR_IIDR_Type_Revision (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_IIDR_Type_Revision r v)


def _set_GITS_IIDR_Type_Revision (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GITS_IIDR_Type_Revision r v)


def _set_MIDR_Type_Revision (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MIDR_Type_Revision r v)


def _set_PMIIDR_Type_Revision (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMIIDR_Type_Revision r v)


def _set_SMIDR_EL1_Type_Revision (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SMIDR_EL1_Type_Revision r v)


def _set_VPIDR_EL2_Type_Revision (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VPIDR_EL2_Type_Revision r v)


def _set_VPIDR_Type_Revision (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_VPIDR_Type_Revision r v)


def _set_MIDR_EL1_Type_Variant (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MIDR_EL1_Type_Variant r v)


def _set_AMIIDR_Type_Variant (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMIIDR_Type_Variant r v)


def _set_FPSID_Type_Variant (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSID_Type_Variant r v)


def _set_GICD_IIDR_Type_Variant (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_IIDR_Type_Variant r v)


def _set_GICM_IIDR_Type_Variant (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICM_IIDR_Type_Variant r v)


def _set_GICR_IIDR_Type_Variant (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_IIDR_Type_Variant r v)


def _set_GITS_IIDR_Type_Variant (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GITS_IIDR_Type_Variant r v)


def _set_MIDR_Type_Variant (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MIDR_Type_Variant r v)


def _set_PMIIDR_Type_Variant (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMIIDR_Type_Variant r v)


def _set_VPIDR_EL2_Type_Variant (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VPIDR_EL2_Type_Variant r v)


def _set_VPIDR_Type_Variant (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_VPIDR_Type_Variant r v)


def _set_ICC_RPR_EL1_Type_NMI_NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_RPR_EL1_Type_NMI_NS r v)


def _set_ICC_SGI0R_EL1_Type_Aff1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI0R_EL1_Type_Aff1 r v)


def _set_GITS_MPIDR_Type_Aff1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GITS_MPIDR_Type_Aff1 r v)


def _set_ICC_ASGI1R_EL1_Type_Aff1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_ASGI1R_EL1_Type_Aff1 r v)


def _set_ICC_ASGI1R_Type_Aff1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_ASGI1R_Type_Aff1 r v)


def _set_ICC_SGI0R_Type_Aff1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI0R_Type_Aff1 r v)


def _set_ICC_SGI1R_EL1_Type_Aff1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI1R_EL1_Type_Aff1 r v)


def _set_ICC_SGI1R_Type_Aff1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI1R_Type_Aff1 r v)


def _set_MPIDR_EL1_Type_Aff1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPIDR_EL1_Type_Aff1 r v)


def _set_MPIDR_Type_Aff1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MPIDR_Type_Aff1 r v)


def _set_VMPIDR_EL2_Type_Aff1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VMPIDR_EL2_Type_Aff1 r v)


def _set_VMPIDR_Type_Aff1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_VMPIDR_Type_Aff1 r v)


def _set_ICC_SGI0R_EL1_Type_Aff2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI0R_EL1_Type_Aff2 r v)


def _set_GITS_MPIDR_Type_Aff2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GITS_MPIDR_Type_Aff2 r v)


def _set_ICC_ASGI1R_EL1_Type_Aff2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_ASGI1R_EL1_Type_Aff2 r v)


def _set_ICC_ASGI1R_Type_Aff2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_ASGI1R_Type_Aff2 r v)


def _set_ICC_SGI0R_Type_Aff2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI0R_Type_Aff2 r v)


def _set_ICC_SGI1R_EL1_Type_Aff2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI1R_EL1_Type_Aff2 r v)


def _set_ICC_SGI1R_Type_Aff2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI1R_Type_Aff2 r v)


def _set_MPIDR_EL1_Type_Aff2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPIDR_EL1_Type_Aff2 r v)


def _set_MPIDR_Type_Aff2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_MPIDR_Type_Aff2 r v)


def _set_VMPIDR_EL2_Type_Aff2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VMPIDR_EL2_Type_Aff2 r v)


def _set_VMPIDR_Type_Aff2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_VMPIDR_Type_Aff2 r v)


def _set_ICC_SGI0R_EL1_Type_Aff3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI0R_EL1_Type_Aff3 r v)


def _set_GITS_MPIDR_Type_Aff3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GITS_MPIDR_Type_Aff3 r v)


def _set_ICC_ASGI1R_EL1_Type_Aff3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_ASGI1R_EL1_Type_Aff3 r v)


def _set_ICC_ASGI1R_Type_Aff3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_ASGI1R_Type_Aff3 r v)


def _set_ICC_SGI0R_Type_Aff3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI0R_Type_Aff3 r v)


def _set_ICC_SGI1R_EL1_Type_Aff3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI1R_EL1_Type_Aff3 r v)


def _set_ICC_SGI1R_Type_Aff3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI1R_Type_Aff3 r v)


def _set_MPIDR_EL1_Type_Aff3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MPIDR_EL1_Type_Aff3 r v)


def _set_VMPIDR_EL2_Type_Aff3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VMPIDR_EL2_Type_Aff3 r v)


def _set_ICC_SGI0R_EL1_Type_IRM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI0R_EL1_Type_IRM r v)


def _set_ICC_ASGI1R_EL1_Type_IRM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_ASGI1R_EL1_Type_IRM r v)


def _set_ICC_ASGI1R_Type_IRM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_ASGI1R_Type_IRM r v)


def _set_ICC_SGI0R_Type_IRM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI0R_Type_IRM r v)


def _set_ICC_SGI1R_EL1_Type_IRM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI1R_EL1_Type_IRM r v)


def _set_ICC_SGI1R_Type_IRM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI1R_Type_IRM r v)


def _set_ICC_SGI0R_EL1_Type_RS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI0R_EL1_Type_RS r v)


def _set_ICC_ASGI1R_EL1_Type_RS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_ASGI1R_EL1_Type_RS r v)


def _set_ICC_ASGI1R_Type_RS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_ASGI1R_Type_RS r v)


def _set_ICC_SGI0R_Type_RS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI0R_Type_RS r v)


def _set_ICC_SGI1R_EL1_Type_RS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI1R_EL1_Type_RS r v)


def _set_ICC_SGI1R_Type_RS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI1R_Type_RS r v)


def _set_ICC_SGI0R_EL1_Type_TargetList (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI0R_EL1_Type_TargetList r v)


def _set_ICC_ASGI1R_EL1_Type_TargetList (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_ASGI1R_EL1_Type_TargetList r v)


def _set_ICC_ASGI1R_Type_TargetList (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_ASGI1R_Type_TargetList r v)


def _set_ICC_SGI0R_Type_TargetList (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI0R_Type_TargetList r v)


def _set_ICC_SGI1R_EL1_Type_TargetList (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI1R_EL1_Type_TargetList r v)


def _set_ICC_SGI1R_Type_TargetList (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_SGI1R_Type_TargetList r v)


def _set_SPMACCESSR_EL1_Type_P31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPMACCESSR_EL1_Type_P31 r v)


def _set_ICH_AP0R_EL2_Type_P31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_AP0R_EL2_Type_P31 r v)


def _set_ICH_AP0R_Type_P31 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_AP0R_Type_P31 r v)


def _set_ICH_AP1R_EL2_Type_P31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_AP1R_EL2_Type_P31 r v)


def _set_ICH_AP1R_Type_P31 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_AP1R_Type_P31 r v)


def _set_SPMACCESSR_EL2_Type_P31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPMACCESSR_EL2_Type_P31 r v)


def _set_SPMACCESSR_EL3_Type_P31 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPMACCESSR_EL3_Type_P31 r v)


def _set_SPMSELR_EL0_Type_SYSPMUSEL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPMSELR_EL0_Type_SYSPMUSEL r v)


def __get_selected_SPMACCESSR_EL1_field (_ : Unit) : SailM (BitVec 2) := do
  let w__0 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
  let idx : Int := ((BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__0)) *i 2)
  let w__1 ← (( do readReg SPMACCESSR_EL1 ) : SailM (BitVec 64) )
  (pure ((BitVec.slice w__1 (Sail.Int.toNatChecked (idx)) 2)))


def _set_ID_AA64PFR1_EL1_Type_CSV2_frac (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_CSV2_frac r v)


def _set_ID_AA64PFR1_EL1_Type_DF2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_DF2 r v)


def _set_ID_AA64PFR1_EL1_Type_GCS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_GCS r v)


def _set_EDHSR_Type_GCS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDHSR_Type_GCS r v)


def _set_ID_AA64PFR1_EL1_Type_MPAM_frac (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_MPAM_frac r v)


def _set_ID_AA64PFR1_EL1_Type_MTE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_MTE r v)


def _set_ID_AA64PFR1_EL1_Type_MTEX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_MTEX r v)


def _set_ID_AA64PFR1_EL1_Type_MTE_frac (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_MTE_frac r v)


def _set_ID_AA64PFR1_EL1_Type_PFAR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_PFAR r v)


def _set_ID_AA64PFR1_EL1_Type_RAS_frac (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_RAS_frac r v)


def _set_ID_PFR2_EL1_Type_RAS_frac (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_PFR2_EL1_Type_RAS_frac r v)


def _set_ID_PFR2_Type_RAS_frac (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_PFR2_Type_RAS_frac r v)


def _set_ID_AA64PFR1_EL1_Type_RNDR_trap (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_RNDR_trap r v)


def _set_ID_AA64PFR1_EL1_Type_SME (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_SME r v)


def _set_ID_AA64PFR1_EL1_Type_THE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64PFR1_EL1_Type_THE r v)


def _set_ID_AA64PFR0_EL1_Type_AMU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64PFR0_EL1_Type_AMU r v)


def _set_EDPFR_Type_AMU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDPFR_Type_AMU r v)


def _set_ID_PFR0_EL1_Type_AMU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_PFR0_EL1_Type_AMU r v)


def _set_ID_PFR0_Type_AMU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_PFR0_Type_AMU r v)


end ArmFull.Functions
