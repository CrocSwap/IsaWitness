import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0057
import ArmFull.Fn.M0058
import ArmFull.Fn.M0069
import ArmFull.Fn.M0073
import ArmFull.Fn.M0074
import ArmFull.Fn.M0075

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

def _set_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 r v)


def _set_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 r v)


def _set_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 r v)


def _set_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 r v)


def _set_HDFGWTR2_EL2_Type_nSPMINTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nSPMINTEN r v)


def _set_HDFGRTR2_EL2_Type_nSPMINTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nSPMINTEN r v)


def _set_HDFGWTR2_EL2_Type_nSPMOVS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nSPMOVS r v)


def _set_HDFGRTR2_EL2_Type_nSPMOVS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nSPMOVS r v)


def _set_HDFGWTR2_EL2_Type_nSPMSCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nSPMSCR_EL1 r v)


def _set_HDFGRTR2_EL2_Type_nSPMSCR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nSPMSCR_EL1 r v)


def _set_HDFGWTR2_EL2_Type_nSPMSELR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGWTR2_EL2_Type_nSPMSELR_EL0 r v)


def _set_HDFGRTR2_EL2_Type_nSPMSELR_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HDFGRTR2_EL2_Type_nSPMSELR_EL0 r v)


def _set_ID_ISAR0_EL1_Type_BitCount (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_ISAR0_EL1_Type_BitCount r v)


def _set_ID_ISAR0_Type_BitCount (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_ISAR0_Type_BitCount r v)


def _set_ID_ISAR0_EL1_Type_BitField (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_ISAR0_EL1_Type_BitField r v)


def _set_ID_ISAR0_Type_BitField (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_ISAR0_Type_BitField r v)


def _set_ID_ISAR0_EL1_Type_CmpBranch (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_ISAR0_EL1_Type_CmpBranch r v)


def _set_ID_ISAR0_Type_CmpBranch (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_ISAR0_Type_CmpBranch r v)


def _set_ID_ISAR0_EL1_Type_Coproc (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_ISAR0_EL1_Type_Coproc r v)


def _set_ID_ISAR0_Type_Coproc (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_ISAR0_Type_Coproc r v)


def _set_ID_ISAR0_EL1_Type_Debug (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_ISAR0_EL1_Type_Debug r v)


def _set_ID_ISAR0_Type_Debug (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_ISAR0_Type_Debug r v)


def _set_ID_ISAR0_EL1_Type_Divide (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_ISAR0_EL1_Type_Divide r v)


def _set_ID_ISAR0_Type_Divide (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_ISAR0_Type_Divide r v)


def _set_ID_ISAR0_EL1_Type_Swap (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_ISAR0_EL1_Type_Swap r v)


def _set_ID_ISAR0_Type_Swap (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_ISAR0_Type_Swap r v)


def __get_selected_SPMACCESSR_EL2_field (_ : Unit) : SailM (BitVec 2) := do
  let w__0 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
  let idx : Int := ((BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__0)) *i 2)
  let w__1 ← (( do readReg SPMACCESSR_EL2 ) : SailM (BitVec 64) )
  (pure ((BitVec.slice w__1 (Sail.Int.toNatChecked (idx)) 2)))


def _set_MDRAR_EL1_Type_ROMADDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 44)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDRAR_EL1_Type_ROMADDR r v)


def _set_DBGDRAR_Type_ROMADDR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 36)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGDRAR_Type_ROMADDR r v)


def _set_MDRAR_EL1_Type_Valid (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDRAR_EL1_Type_Valid r v)


def _set_DBGDRAR_Type_Valid (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGDRAR_Type_Valid r v)


def _set_GICM_TYPER_Type_Valid (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICM_TYPER_Type_Valid r v)


def _set_GICR_VPENDBASER_Type_Valid (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_VPENDBASER_Type_Valid r v)


def _set_GICR_VPROPBASER_Type_Valid (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_VPROPBASER_Type_Valid r v)


def _set_GITS_CBASER_Type_Valid (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GITS_CBASER_Type_Valid r v)


def _set_LORSA_EL1_Type_Valid (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_LORSA_EL1_Type_Valid r v)


def _set_ICC_IGRPEN1_EL3_Type_EnableGrp1NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_IGRPEN1_EL3_Type_EnableGrp1NS r v)


def _set_GICD_CTLR_Type_EnableGrp1NS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_CTLR_Type_EnableGrp1NS r v)


def _set_ICC_MGRPEN1_Type_EnableGrp1NS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICC_MGRPEN1_Type_EnableGrp1NS r v)


def _set_ICC_IGRPEN1_EL3_Type_EnableGrp1S (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_IGRPEN1_EL3_Type_EnableGrp1S r v)


def _set_GICD_CTLR_Type_EnableGrp1S (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_CTLR_Type_EnableGrp1S r v)


def _set_ICC_MGRPEN1_Type_EnableGrp1S (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICC_MGRPEN1_Type_EnableGrp1S r v)


def _set_ID_MMFR1_EL1_Type_BPred (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR1_EL1_Type_BPred r v)


def _set_ID_MMFR1_Type_BPred (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR1_Type_BPred r v)


def _set_ID_MMFR1_EL1_Type_L1Hvd (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR1_EL1_Type_L1Hvd r v)


def _set_ID_MMFR1_Type_L1Hvd (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR1_Type_L1Hvd r v)


def _set_ID_MMFR1_EL1_Type_L1HvdSW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR1_EL1_Type_L1HvdSW r v)


def _set_ID_MMFR1_Type_L1HvdSW (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR1_Type_L1HvdSW r v)


def _set_ID_MMFR1_EL1_Type_L1HvdVA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR1_EL1_Type_L1HvdVA r v)


def _set_ID_MMFR1_Type_L1HvdVA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR1_Type_L1HvdVA r v)


def _set_ID_MMFR1_EL1_Type_L1TstCln (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR1_EL1_Type_L1TstCln r v)


def _set_ID_MMFR1_Type_L1TstCln (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR1_Type_L1TstCln r v)


def _set_ID_MMFR1_EL1_Type_L1Uni (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR1_EL1_Type_L1Uni r v)


def _set_ID_MMFR1_Type_L1Uni (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR1_Type_L1Uni r v)


def _set_ID_MMFR1_EL1_Type_L1UniSW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR1_EL1_Type_L1UniSW r v)


def _set_ID_MMFR1_Type_L1UniSW (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR1_Type_L1UniSW r v)


def _set_ID_MMFR1_EL1_Type_L1UniVA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR1_EL1_Type_L1UniVA r v)


def _set_ID_MMFR1_Type_L1UniVA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR1_Type_L1UniVA r v)


def _set_ID_AA64MMFR1_EL1_Type_AFP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_AFP r v)


def _set_ID_AA64MMFR1_EL1_Type_ECBHB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_ECBHB r v)


def _set_ID_AA64MMFR1_EL1_Type_HAFDBS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_HAFDBS r v)


def _set_ID_AA64MMFR1_EL1_Type_HCX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_HCX r v)


def _set_ID_AA64MMFR1_EL1_Type_LO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_LO r v)


def _set_ID_AA64MMFR1_EL1_Type_TIDCP1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_TIDCP1 r v)


def _set_ID_AA64MMFR1_EL1_Type_TWED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_TWED r v)


def _set_ID_AA64MMFR1_EL1_Type_VH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_VH r v)


def _set_ID_AA64MMFR1_EL1_Type_VMIDBits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR1_EL1_Type_VMIDBits r v)


def _set_ID_MMFR0_EL1_Type_AuxReg (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR0_EL1_Type_AuxReg r v)


def _set_ID_MMFR0_Type_AuxReg (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR0_Type_AuxReg r v)


def _set_ID_MMFR0_EL1_Type_FCSE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR0_EL1_Type_FCSE r v)


def _set_ID_MMFR0_Type_FCSE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR0_Type_FCSE r v)


def _set_ID_MMFR0_EL1_Type_InnerShr (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR0_EL1_Type_InnerShr r v)


def _set_ID_MMFR0_Type_InnerShr (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR0_Type_InnerShr r v)


def _set_ID_MMFR0_EL1_Type_OuterShr (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR0_EL1_Type_OuterShr r v)


def _set_ID_MMFR0_Type_OuterShr (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR0_Type_OuterShr r v)


def _set_ID_MMFR0_EL1_Type_PMSA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR0_EL1_Type_PMSA r v)


def _set_EDAA32PFR_Type_PMSA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDAA32PFR_Type_PMSA r v)


def _set_ID_MMFR0_Type_PMSA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR0_Type_PMSA r v)


def _set_ID_MMFR0_EL1_Type_ShareLvl (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR0_EL1_Type_ShareLvl r v)


def _set_ID_MMFR0_Type_ShareLvl (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR0_Type_ShareLvl r v)


def _set_ID_MMFR0_EL1_Type_TCM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR0_EL1_Type_TCM r v)


def _set_ID_MMFR0_Type_TCM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR0_Type_TCM r v)


def _set_ID_MMFR0_EL1_Type_VMSA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_MMFR0_EL1_Type_VMSA r v)


def _set_EDAA32PFR_Type_VMSA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDAA32PFR_Type_VMSA r v)


def _set_ID_MMFR0_Type_VMSA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_MMFR0_Type_VMSA r v)


def _set_ICH_VMCR_EL2_Type_VAckCtl (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_VMCR_EL2_Type_VAckCtl r v)


def _set_GICH_VMCR_Type_VAckCtl (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_VMCR_Type_VAckCtl r v)


def _set_ICH_VMCR_Type_VAckCtl (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_VMCR_Type_VAckCtl r v)


def _set_ICH_VMCR_EL2_Type_VBPR0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_VMCR_EL2_Type_VBPR0 r v)


def _set_GICH_VMCR_Type_VBPR0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_VMCR_Type_VBPR0 r v)


def _set_ICH_VMCR_Type_VBPR0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_VMCR_Type_VBPR0 r v)


def _set_ICH_VMCR_EL2_Type_VBPR1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_VMCR_EL2_Type_VBPR1 r v)


def _set_GICH_VMCR_Type_VBPR1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_VMCR_Type_VBPR1 r v)


def _set_ICH_VMCR_Type_VBPR1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_VMCR_Type_VBPR1 r v)


def _set_ICH_VMCR_EL2_Type_VCBPR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_VMCR_EL2_Type_VCBPR r v)


def _set_GICH_VMCR_Type_VCBPR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_VMCR_Type_VCBPR r v)


def _set_ICH_VMCR_Type_VCBPR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_VMCR_Type_VCBPR r v)


def _set_ICH_VMCR_EL2_Type_VENG0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_VMCR_EL2_Type_VENG0 r v)


def _set_GICH_VMCR_Type_VENG0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_VMCR_Type_VENG0 r v)


def _set_ICH_VMCR_Type_VENG0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_VMCR_Type_VENG0 r v)


def _set_ICH_VMCR_EL2_Type_VENG1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_VMCR_EL2_Type_VENG1 r v)


def _set_GICH_VMCR_Type_VENG1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_VMCR_Type_VENG1 r v)


def _set_ICH_VMCR_Type_VENG1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_VMCR_Type_VENG1 r v)


def _set_ICH_VMCR_EL2_Type_VEOIM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_VMCR_EL2_Type_VEOIM r v)


def _set_GICH_VMCR_Type_VEOIM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_VMCR_Type_VEOIM r v)


def _set_ICH_VMCR_Type_VEOIM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_VMCR_Type_VEOIM r v)


def _set_ICH_VMCR_EL2_Type_VFIQEn (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_VMCR_EL2_Type_VFIQEn r v)


def _set_GICH_VMCR_Type_VFIQEn (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_VMCR_Type_VFIQEn r v)


def _set_ICH_VMCR_Type_VFIQEn (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_VMCR_Type_VFIQEn r v)


def _set_ICH_VMCR_EL2_Type_VPMR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_VMCR_EL2_Type_VPMR r v)


def _set_GICH_VMCR_Type_VPMR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_VMCR_Type_VPMR r v)


def _set_ICH_VMCR_Type_VPMR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_VMCR_Type_VPMR r v)


def _set_ICC_CTLR_EL3_Type_CBPR_EL1NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_CTLR_EL3_Type_CBPR_EL1NS r v)


def _set_ICC_MCTLR_Type_CBPR_EL1NS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICC_MCTLR_Type_CBPR_EL1NS r v)


def _set_ICC_CTLR_EL3_Type_CBPR_EL1S (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_CTLR_EL3_Type_CBPR_EL1S r v)


def _set_ICC_MCTLR_Type_CBPR_EL1S (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICC_MCTLR_Type_CBPR_EL1S r v)


def _set_ICC_CTLR_EL3_Type_EOImode_EL1NS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_CTLR_EL3_Type_EOImode_EL1NS r v)


def _set_ICC_MCTLR_Type_EOImode_EL1NS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICC_MCTLR_Type_EOImode_EL1NS r v)


def _set_ICC_CTLR_EL3_Type_EOImode_EL1S (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_CTLR_EL3_Type_EOImode_EL1S r v)


def _set_ICC_MCTLR_Type_EOImode_EL1S (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICC_MCTLR_Type_EOImode_EL1S r v)


def _set_ICC_CTLR_EL3_Type_EOImode_EL3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_CTLR_EL3_Type_EOImode_EL3 r v)


def _set_ICC_MCTLR_Type_EOImode_EL3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICC_MCTLR_Type_EOImode_EL3 r v)


def _set_ICC_CTLR_EL3_Type_RM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_CTLR_EL3_Type_RM r v)


def _set_ICC_MCTLR_Type_RM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICC_MCTLR_Type_RM r v)


def _set_ICC_CTLR_EL3_Type_nDS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_CTLR_EL3_Type_nDS r v)


def _set_ICC_MCTLR_Type_nDS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICC_MCTLR_Type_nDS r v)


def _set_ID_AA64PFR2_EL1_Type_MTEFAR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64PFR2_EL1_Type_MTEFAR r v)


def _set_ID_AA64PFR2_EL1_Type_MTEPERM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64PFR2_EL1_Type_MTEPERM r v)


def _set_ID_AA64PFR2_EL1_Type_MTESTOREONLY (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64PFR2_EL1_Type_MTESTOREONLY r v)


def _set_CCSIDR2_EL1_Type_NumSets (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CCSIDR2_EL1_Type_NumSets r v)


def _set_CCSIDR2_Type_NumSets (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 24)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CCSIDR2_Type_NumSets r v)


def _set_CCSIDR_Type_NumSets (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 15)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CCSIDR_Type_NumSets r v)


def _set_ID_AA64ISAR2_EL1_Type_APA3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_APA3 r v)


def _set_ID_AA64ISAR2_EL1_Type_BC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_BC r v)


def _set_ID_AA64ISAR2_EL1_Type_CSSC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_CSSC r v)


def _set_ID_AA64ISAR2_EL1_Type_GPA3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_GPA3 r v)


def _set_ID_AA64ISAR2_EL1_Type_MOPS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_MOPS r v)


def _set_ID_AA64ISAR2_EL1_Type_PAC_frac (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_PAC_frac r v)


def _set_ID_AA64ISAR2_EL1_Type_PRFMSLC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_PRFMSLC r v)


def _set_ID_AA64ISAR2_EL1_Type_RPRES (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_RPRES r v)


def _set_ID_AA64ISAR2_EL1_Type_RPRFM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_RPRFM r v)


def _set_ID_AA64ISAR2_EL1_Type_SYSINSTR_128 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_SYSINSTR_128 r v)


def _set_ID_AA64ISAR2_EL1_Type_SYSREG_128 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_SYSREG_128 r v)


def _set_ID_AA64ISAR2_EL1_Type_WFxT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR2_EL1_Type_WFxT r v)


def _set_HFGRTR2_EL2_Type_nERXGSR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR2_EL2_Type_nERXGSR_EL1 r v)


def _set_HFGRTR2_EL2_Type_nPFAR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR2_EL2_Type_nPFAR_EL1 r v)


def _set_HFGWTR2_EL2_Type_nPFAR_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR2_EL2_Type_nPFAR_EL1 r v)


def _set_HFGRTR2_EL2_Type_nRCWSMASK_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGRTR2_EL2_Type_nRCWSMASK_EL1 r v)


def _set_HFGWTR2_EL2_Type_nRCWSMASK_EL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HFGWTR2_EL2_Type_nRCWSMASK_EL1 r v)


def _set_ID_ISAR5_EL1_Type_SEVL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_ISAR5_EL1_Type_SEVL r v)


end ArmFull.Functions
