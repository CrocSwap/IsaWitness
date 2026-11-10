import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork

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

def _get_ID_ISAR0_Type_BitField (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _get_ID_ISAR0_EL1_Type_CmpBranch (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _update_ID_ISAR0_EL1_Type_CmpBranch (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _get_ID_ISAR0_Type_CmpBranch (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _get_ID_ISAR0_EL1_Type_Coproc (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_ID_ISAR0_EL1_Type_Coproc (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_ID_ISAR0_Type_Coproc (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_ID_ISAR0_EL1_Type_Debug (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _update_ID_ISAR0_EL1_Type_Debug (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _get_ID_ISAR0_Type_Debug (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _get_ID_ISAR0_EL1_Type_Divide (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _update_ID_ISAR0_EL1_Type_Divide (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _get_ID_ISAR0_Type_Divide (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_ID_ISAR0_EL1_Type_Swap (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_ID_ISAR0_EL1_Type_Swap (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_ID_ISAR0_Type_Swap (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def __set_CNTHP_CTL_EL2 (value_name : (BitVec 64)) : SailM Unit := do
  let r : CNTHP_CTL_EL2_Type := value_name
  let w__0 ← (( do readReg CNTHP_CTL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHP_CTL_EL2 (Sail.BitVec.updateSubrange w__0 1 0 (BitVec.slice r 0 2))
  let w__1 ← (( do readReg CNTHP_CTL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHP_CTL_EL2 (Sail.BitVec.updateSubrange w__1 63 3 (BitVec.slice r 3 61))


def Mk_CNTHVS_TVAL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_CNTHP_TVAL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_SPMACCESSR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_SPMACCESSR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_PMZR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_PMICNTSVR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_PMICNTSVR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_MDRAR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_MDRAR_EL1_Type_ROMADDR (v : (BitVec 64)) : (BitVec 44) :=
  (Sail.BitVec.extractLsb v 55 12)


def _update_MDRAR_EL1_Type_ROMADDR (v : (BitVec 64)) (x : (BitVec 44)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 12 x)


def _update_DBGDRAR_Type_ROMADDR (v : (BitVec 64)) (x : (BitVec 36)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 12 x)


def _get_DBGDRAR_Type_ROMADDR (v : (BitVec 64)) : (BitVec 36) :=
  (Sail.BitVec.extractLsb v 47 12)


def _get_MDRAR_EL1_Type_Valid (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)


def _update_MDRAR_EL1_Type_Valid (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 0 x)


def _update_DBGDRAR_Type_Valid (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 0 x)


def _update_GICM_TYPER_Type_Valid (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_GICR_VPENDBASER_Type_Valid (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)


def _update_GICR_VPROPBASER_Type_Valid (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)


def _update_GITS_CBASER_Type_Valid (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)


def _update_LORSA_EL1_Type_Valid (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_DBGDRAR_Type_Valid (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)


def _get_GICM_TYPER_Type_Valid (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_GICR_VPENDBASER_Type_Valid (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)


def _get_GICR_VPROPBASER_Type_Valid (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)


def _get_GITS_CBASER_Type_Valid (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)


def _get_LORSA_EL1_Type_Valid (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def Mk_ICC_IGRPEN1_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ICC_IGRPEN1_EL3_Type_EnableGrp1NS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_ICC_IGRPEN1_EL3_Type_EnableGrp1NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_GICD_CTLR_Type_EnableGrp1NS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_ICC_MGRPEN1_Type_EnableGrp1NS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_GICD_CTLR_Type_EnableGrp1NS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_ICC_MGRPEN1_Type_EnableGrp1NS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_ICC_IGRPEN1_EL3_Type_EnableGrp1S (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_ICC_IGRPEN1_EL3_Type_EnableGrp1S (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_GICD_CTLR_Type_EnableGrp1S (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_ICC_MGRPEN1_Type_EnableGrp1S (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_GICD_CTLR_Type_EnableGrp1S (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_ICC_MGRPEN1_Type_EnableGrp1S (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def Mk_ID_MMFR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ID_MMFR1_EL1_Type_BPred (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _update_ID_MMFR1_EL1_Type_BPred (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _get_ID_MMFR1_Type_BPred (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _get_ID_MMFR1_EL1_Type_L1Hvd (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_ID_MMFR1_EL1_Type_L1Hvd (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_ID_MMFR1_Type_L1Hvd (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_ID_MMFR1_EL1_Type_L1HvdSW (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _update_ID_MMFR1_EL1_Type_L1HvdSW (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_ID_MMFR1_Type_L1HvdSW (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _get_ID_MMFR1_EL1_Type_L1HvdVA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_ID_MMFR1_EL1_Type_L1HvdVA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_ID_MMFR1_Type_L1HvdVA (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_ID_MMFR1_EL1_Type_L1TstCln (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _update_ID_MMFR1_EL1_Type_L1TstCln (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _get_ID_MMFR1_Type_L1TstCln (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_ID_MMFR1_EL1_Type_L1Uni (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _update_ID_MMFR1_EL1_Type_L1Uni (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _get_ID_MMFR1_Type_L1Uni (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _get_ID_MMFR1_EL1_Type_L1UniSW (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _update_ID_MMFR1_EL1_Type_L1UniSW (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _get_ID_MMFR1_Type_L1UniSW (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _get_ID_MMFR1_EL1_Type_L1UniVA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_ID_MMFR1_EL1_Type_L1UniVA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_ID_MMFR1_Type_L1UniVA (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def Mk_LORSA_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_ID_AA64MMFR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ID_AA64MMFR1_EL1_Type_AFP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)


def _update_ID_AA64MMFR1_EL1_Type_AFP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)


def _get_ID_AA64MMFR1_EL1_Type_ECBHB (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)


def _update_ID_AA64MMFR1_EL1_Type_ECBHB (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)


def _get_ID_AA64MMFR1_EL1_Type_HAFDBS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_ID_AA64MMFR1_EL1_Type_HAFDBS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_ID_AA64MMFR1_EL1_Type_HCX (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)


def _update_ID_AA64MMFR1_EL1_Type_HCX (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)


def _get_ID_AA64MMFR1_EL1_Type_LO (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_ID_AA64MMFR1_EL1_Type_LO (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_ID_AA64MMFR1_EL1_Type_TIDCP1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)


def _update_ID_AA64MMFR1_EL1_Type_TIDCP1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)


def _get_ID_AA64MMFR1_EL1_Type_TWED (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)


def _update_ID_AA64MMFR1_EL1_Type_TWED (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)


def _get_ID_AA64MMFR1_EL1_Type_VH (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _update_ID_AA64MMFR1_EL1_Type_VH (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_ID_AA64MMFR1_EL1_Type_VMIDBits (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_ID_AA64MMFR1_EL1_Type_VMIDBits (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def Mk_PMSWINC_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def __set_CNTV_CTL_EL0 (value_name : (BitVec 64)) : SailM Unit := do
  let r : CNTV_CTL_EL0_Type := value_name
  let w__0 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
  writeReg CNTV_CTL_EL0 (Sail.BitVec.updateSubrange w__0 1 0 (BitVec.slice r 0 2))
  let w__1 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
  writeReg CNTV_CTL_EL0 (Sail.BitVec.updateSubrange w__1 63 3 (BitVec.slice r 3 61))


def undefined_PMIAR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_PMIAR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_ID_MMFR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ID_MMFR0_EL1_Type_AuxReg (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _update_ID_MMFR0_EL1_Type_AuxReg (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _get_ID_MMFR0_Type_AuxReg (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _get_ID_MMFR0_EL1_Type_FCSE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _update_ID_MMFR0_EL1_Type_FCSE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _get_ID_MMFR0_Type_FCSE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_ID_MMFR0_EL1_Type_InnerShr (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _update_ID_MMFR0_EL1_Type_InnerShr (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _get_ID_MMFR0_Type_InnerShr (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _get_ID_MMFR0_EL1_Type_OuterShr (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _update_ID_MMFR0_EL1_Type_OuterShr (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_ID_MMFR0_Type_OuterShr (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _get_ID_MMFR0_EL1_Type_PMSA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_ID_MMFR0_EL1_Type_PMSA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_EDAA32PFR_Type_PMSA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_EDAA32PFR_Type_PMSA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_ID_MMFR0_Type_PMSA (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_ID_MMFR0_EL1_Type_ShareLvl (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _update_ID_MMFR0_EL1_Type_ShareLvl (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _get_ID_MMFR0_Type_ShareLvl (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _get_ID_MMFR0_EL1_Type_TCM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_ID_MMFR0_EL1_Type_TCM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_ID_MMFR0_Type_TCM (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_ID_MMFR0_EL1_Type_VMSA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_ID_MMFR0_EL1_Type_VMSA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_EDAA32PFR_Type_VMSA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_EDAA32PFR_Type_VMSA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_ID_MMFR0_Type_VMSA (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def Mk_ICH_VMCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ICH_VMCR_EL2_Type_VAckCtl (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_ICH_VMCR_EL2_Type_VAckCtl (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_GICH_VMCR_Type_VAckCtl (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_ICH_VMCR_Type_VAckCtl (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_GICH_VMCR_Type_VAckCtl (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_ICH_VMCR_Type_VAckCtl (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_ICH_VMCR_EL2_Type_VBPR0 (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 23 21)


def _update_ICH_VMCR_EL2_Type_VBPR0 (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 21 x)


def _update_GICH_VMCR_Type_VBPR0 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 21 x)


def _update_ICH_VMCR_Type_VBPR0 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 21 x)


def _get_GICH_VMCR_Type_VBPR0 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 23 21)


def _get_ICH_VMCR_Type_VBPR0 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 23 21)


def _get_ICH_VMCR_EL2_Type_VBPR1 (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 20 18)


def _update_ICH_VMCR_EL2_Type_VBPR1 (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 18 x)


def _update_GICH_VMCR_Type_VBPR1 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 18 x)


def _update_ICH_VMCR_Type_VBPR1 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 18 x)


def _get_GICH_VMCR_Type_VBPR1 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 20 18)


def _get_ICH_VMCR_Type_VBPR1 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 20 18)


def _get_ICH_VMCR_EL2_Type_VCBPR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _update_ICH_VMCR_EL2_Type_VCBPR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _update_GICH_VMCR_Type_VCBPR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _update_ICH_VMCR_Type_VCBPR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_GICH_VMCR_Type_VCBPR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _get_ICH_VMCR_Type_VCBPR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _get_ICH_VMCR_EL2_Type_VENG0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_ICH_VMCR_EL2_Type_VENG0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_GICH_VMCR_Type_VENG0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_ICH_VMCR_Type_VENG0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_GICH_VMCR_Type_VENG0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_ICH_VMCR_Type_VENG0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_ICH_VMCR_EL2_Type_VENG1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_ICH_VMCR_EL2_Type_VENG1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_GICH_VMCR_Type_VENG1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_ICH_VMCR_Type_VENG1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_GICH_VMCR_Type_VENG1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_ICH_VMCR_Type_VENG1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_ICH_VMCR_EL2_Type_VEOIM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def _update_ICH_VMCR_EL2_Type_VEOIM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


def _update_GICH_VMCR_Type_VEOIM (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


def _update_ICH_VMCR_Type_VEOIM (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


def _get_GICH_VMCR_Type_VEOIM (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def _get_ICH_VMCR_Type_VEOIM (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def _get_ICH_VMCR_EL2_Type_VFIQEn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_ICH_VMCR_EL2_Type_VFIQEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_GICH_VMCR_Type_VFIQEn (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_ICH_VMCR_Type_VFIQEn (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_GICH_VMCR_Type_VFIQEn (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_ICH_VMCR_Type_VFIQEn (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_ICH_VMCR_EL2_Type_VPMR (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)


def _update_ICH_VMCR_EL2_Type_VPMR (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 24 x)


def _update_GICH_VMCR_Type_VPMR (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)


def _update_ICH_VMCR_Type_VPMR (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)


def _get_GICH_VMCR_Type_VPMR (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)


def _get_ICH_VMCR_Type_VPMR (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)


def Mk_VPIDR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_ICC_CTLR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ICC_CTLR_EL3_Type_CBPR_EL1NS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_ICC_CTLR_EL3_Type_CBPR_EL1NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_ICC_MCTLR_Type_CBPR_EL1NS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_ICC_MCTLR_Type_CBPR_EL1NS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_ICC_CTLR_EL3_Type_CBPR_EL1S (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_ICC_CTLR_EL3_Type_CBPR_EL1S (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_ICC_MCTLR_Type_CBPR_EL1S (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


end ArmFull.Functions
