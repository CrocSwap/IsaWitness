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

def _get_ICC_MCTLR_Type_CBPR_EL1S (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_ICC_CTLR_EL3_Type_EOImode_EL1NS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _update_ICC_CTLR_EL3_Type_EOImode_EL1NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _update_ICC_MCTLR_Type_EOImode_EL1NS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_ICC_MCTLR_Type_EOImode_EL1NS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _get_ICC_CTLR_EL3_Type_EOImode_EL1S (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_ICC_CTLR_EL3_Type_EOImode_EL1S (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_ICC_MCTLR_Type_EOImode_EL1S (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_ICC_MCTLR_Type_EOImode_EL1S (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_ICC_CTLR_EL3_Type_EOImode_EL3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_ICC_CTLR_EL3_Type_EOImode_EL3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_ICC_MCTLR_Type_EOImode_EL3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_ICC_MCTLR_Type_EOImode_EL3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_ICC_CTLR_EL3_Type_RM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _update_ICC_CTLR_EL3_Type_RM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_ICC_MCTLR_Type_RM (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _get_ICC_MCTLR_Type_RM (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_ICC_CTLR_EL3_Type_nDS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _update_ICC_CTLR_EL3_Type_nDS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _update_ICC_MCTLR_Type_nDS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _get_ICC_MCTLR_Type_nDS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def Mk_ICC_SRE_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def __set_CNTPS_CTL_EL1 (value_name : (BitVec 64)) : SailM Unit := do
  let r : CNTPS_CTL_EL1_Type := value_name
  let w__0 ← (( do readReg CNTPS_CTL_EL1 ) : SailM (BitVec 64) )
  writeReg CNTPS_CTL_EL1 (Sail.BitVec.updateSubrange w__0 1 0 (BitVec.slice r 0 2))
  let w__1 ← (( do readReg CNTPS_CTL_EL1 ) : SailM (BitVec 64) )
  writeReg CNTPS_CTL_EL1 (Sail.BitVec.updateSubrange w__1 63 3 (BitVec.slice r 3 61))


def Mk_LORC_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_ID_AA64PFR2_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ID_AA64PFR2_EL1_Type_MTEFAR (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _update_ID_AA64PFR2_EL1_Type_MTEFAR (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_ID_AA64PFR2_EL1_Type_MTEPERM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_ID_AA64PFR2_EL1_Type_MTEPERM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_ID_AA64PFR2_EL1_Type_MTESTOREONLY (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_ID_AA64PFR2_EL1_Type_MTESTOREONLY (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def Mk_CCSIDR2_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_CCSIDR2_EL1_Type_NumSets (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _update_CCSIDR2_EL1_Type_NumSets (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_CCSIDR2_Type_NumSets (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)


def _update_CCSIDR_Type_NumSets (v : (BitVec 32)) (x : (BitVec 15)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 13 x)


def _get_CCSIDR2_Type_NumSets (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


def _get_CCSIDR_Type_NumSets (v : (BitVec 32)) : (BitVec 15) :=
  (Sail.BitVec.extractLsb v 27 13)


def Mk_ICC_ASGI1R_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_ID_AA64ISAR2_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ID_AA64ISAR2_EL1_Type_APA3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _update_ID_AA64ISAR2_EL1_Type_APA3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _get_ID_AA64ISAR2_EL1_Type_BC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _update_ID_AA64ISAR2_EL1_Type_BC (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _get_ID_AA64ISAR2_EL1_Type_CSSC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)


def _update_ID_AA64ISAR2_EL1_Type_CSSC (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)


def _get_ID_AA64ISAR2_EL1_Type_GPA3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _update_ID_AA64ISAR2_EL1_Type_GPA3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_ID_AA64ISAR2_EL1_Type_MOPS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_ID_AA64ISAR2_EL1_Type_MOPS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_ID_AA64ISAR2_EL1_Type_PAC_frac (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _update_ID_AA64ISAR2_EL1_Type_PAC_frac (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _get_ID_AA64ISAR2_EL1_Type_PRFMSLC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)


def _update_ID_AA64ISAR2_EL1_Type_PRFMSLC (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)


def _get_ID_AA64ISAR2_EL1_Type_RPRES (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_ID_AA64ISAR2_EL1_Type_RPRES (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_ID_AA64ISAR2_EL1_Type_RPRFM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)


def _update_ID_AA64ISAR2_EL1_Type_RPRFM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)


def _get_ID_AA64ISAR2_EL1_Type_SYSINSTR_128 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)


def _update_ID_AA64ISAR2_EL1_Type_SYSINSTR_128 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)


def _get_ID_AA64ISAR2_EL1_Type_SYSREG_128 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)


def _update_ID_AA64ISAR2_EL1_Type_SYSREG_128 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)


def _get_ID_AA64ISAR2_EL1_Type_WFxT (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_ID_AA64ISAR2_EL1_Type_WFxT (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def Mk_HFGRTR2_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_HFGRTR2_EL2_Type_nERXGSR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_HFGRTR2_EL2_Type_nERXGSR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_HFGRTR2_EL2_Type_nPFAR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_HFGRTR2_EL2_Type_nPFAR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_HFGWTR2_EL2_Type_nPFAR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_HFGWTR2_EL2_Type_nPFAR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_HFGRTR2_EL2_Type_nRCWSMASK_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_HFGRTR2_EL2_Type_nRCWSMASK_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_HFGWTR2_EL2_Type_nRCWSMASK_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_HFGWTR2_EL2_Type_nRCWSMASK_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def Mk_ID_ISAR5_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ID_ISAR5_EL1_Type_SEVL (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_ID_ISAR5_EL1_Type_SEVL (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_ID_ISAR5_Type_SEVL (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_ID_ISAR5_EL1_Type_VCMA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _update_ID_ISAR5_EL1_Type_VCMA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _get_ID_ISAR5_Type_VCMA (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def Mk_RMR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_ICH_HCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ICH_HCR_EL2_Type_DVIM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _update_ICH_HCR_EL2_Type_DVIM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _update_ICH_VTR_EL2_Type_DVIM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)


def _get_ICH_VTR_EL2_Type_DVIM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)


def _get_ICH_HCR_EL2_Type_EOIcount (v : (BitVec 64)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 31 27)


def _update_ICH_HCR_EL2_Type_EOIcount (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 27 x)


def _get_ICH_HCR_Type_EOIcount (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 31 27)


def _get_ICH_HCR_EL2_Type_En (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_ICH_HCR_EL2_Type_En (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_GICH_HCR_Type_En (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_GICH_HCR_Type_En (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_ICH_HCR_Type_En (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_ICH_HCR_EL2_Type_LRENPIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_ICH_HCR_EL2_Type_LRENPIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_GICH_HCR_Type_LRENPIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_GICH_HCR_Type_LRENPIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_ICH_HCR_Type_LRENPIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_ICH_HCR_EL2_Type_NPIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_ICH_HCR_EL2_Type_NPIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_GICH_HCR_Type_NPIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_GICH_HCR_Type_NPIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_ICH_HCR_Type_NPIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_ICH_HCR_EL2_Type_TALL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)


def _update_ICH_HCR_EL2_Type_TALL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _get_ICH_HCR_Type_TALL0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)


def _get_ICH_HCR_EL2_Type_TALL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _update_ICH_HCR_EL2_Type_TALL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _get_ICH_HCR_Type_TALL1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _get_ICH_HCR_EL2_Type_TDIR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _update_ICH_HCR_EL2_Type_TDIR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _get_ICH_HCR_Type_TDIR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _get_ICH_HCR_EL2_Type_TSEI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _update_ICH_HCR_EL2_Type_TSEI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _get_ICH_HCR_Type_TSEI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _get_ICH_HCR_EL2_Type_UIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_ICH_HCR_EL2_Type_UIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_GICH_HCR_Type_UIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_GICH_HCR_Type_UIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_ICH_HCR_Type_UIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_ICH_HCR_EL2_Type_VGrp0DIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _update_ICH_HCR_EL2_Type_VGrp0DIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_GICH_HCR_Type_VGrp0DIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _get_GICH_HCR_Type_VGrp0DIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_ICH_HCR_Type_VGrp0DIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_ICH_HCR_EL2_Type_VGrp0EIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _update_ICH_HCR_EL2_Type_VGrp0EIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _update_GICH_HCR_Type_VGrp0EIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_GICH_HCR_Type_VGrp0EIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _get_ICH_HCR_Type_VGrp0EIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _get_ICH_HCR_EL2_Type_VGrp1DIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _update_ICH_HCR_EL2_Type_VGrp1DIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _update_GICH_HCR_Type_VGrp1DIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _get_GICH_HCR_Type_VGrp1DIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _get_ICH_HCR_Type_VGrp1DIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _get_ICH_HCR_EL2_Type_VGrp1EIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _update_ICH_HCR_EL2_Type_VGrp1EIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_GICH_HCR_Type_VGrp1EIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _get_GICH_HCR_Type_VGrp1EIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_ICH_HCR_Type_VGrp1EIE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_ICH_HCR_EL2_Type_vSGIEOICount (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)


def _update_ICH_HCR_EL2_Type_vSGIEOICount (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)


def _get_ICH_HCR_Type_vSGIEOICount (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)


def Mk_ICC_IGRPEN0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_CNTHPS_TVAL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_ICC_EOIR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_ID_AA64MMFR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ID_AA64MMFR0_EL1_Type_ASIDBits (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_ID_AA64MMFR0_EL1_Type_ASIDBits (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_ID_AA64MMFR0_EL1_Type_BigEnd (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _update_ID_AA64MMFR0_EL1_Type_BigEnd (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_ID_AA64MMFR0_EL1_Type_BigEndEL0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_ID_AA64MMFR0_EL1_Type_BigEndEL0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_ID_AA64MMFR0_EL1_Type_ExS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)


def _update_ID_AA64MMFR0_EL1_Type_ExS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)


def _get_ID_AA64MMFR0_EL1_Type_FGT (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)


def _update_ID_AA64MMFR0_EL1_Type_FGT (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)


def _get_ID_AA64MMFR0_EL1_Type_PARange (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_ID_AA64MMFR0_EL1_Type_PARange (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_ID_AA64MMFR0_EL1_Type_SNSMem (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _update_ID_AA64MMFR0_EL1_Type_SNSMem (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _get_ID_AA64MMFR0_EL1_Type_TGran16 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _update_ID_AA64MMFR0_EL1_Type_TGran16 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _get_ID_AA64MMFR0_EL1_Type_TGran16_2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)


def _update_ID_AA64MMFR0_EL1_Type_TGran16_2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)


def _get_ID_AA64MMFR0_EL1_Type_TGran4 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _update_ID_AA64MMFR0_EL1_Type_TGran4 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _get_ID_AA64MMFR0_EL1_Type_TGran4_2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)


def _update_ID_AA64MMFR0_EL1_Type_TGran4_2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)


def _get_ID_AA64MMFR0_EL1_Type_TGran64 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _update_ID_AA64MMFR0_EL1_Type_TGran64 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _get_ID_AA64MMFR0_EL1_Type_TGran64_2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)


def _update_ID_AA64MMFR0_EL1_Type_TGran64_2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)


def Mk_HDFGRTR2_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_HDFGRTR2_EL2_Type_nPMSSDATA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _update_HDFGRTR2_EL2_Type_nPMSSDATA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _get_HDFGRTR2_EL2_Type_nSPMDEVAFF_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)


def _update_HDFGRTR2_EL2_Type_nSPMDEVAFF_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)


def _get_HDFGRTR2_EL2_Type_nSPMID (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _update_HDFGRTR2_EL2_Type_nSPMID (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def Mk_VMPIDR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_VMPIDR_EL2_Type_Aff0 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _update_VMPIDR_EL2_Type_Aff0 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_MPIDR_EL1_Type_Aff0 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _get_MPIDR_EL1_Type_Aff0 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_MPIDR_Type_Aff0 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_VMPIDR_Type_Aff0 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def Mk_ID_AA64MMFR3_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ID_AA64MMFR3_EL1_Type_ADERR (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)


def _update_ID_AA64MMFR3_EL1_Type_ADERR (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)


def _get_ID_AA64MMFR3_EL1_Type_ANERR (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)


def _update_ID_AA64MMFR3_EL1_Type_ANERR (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)


def _get_ID_AA64MMFR3_EL1_Type_D128_2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)


def _update_ID_AA64MMFR3_EL1_Type_D128_2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)


def _get_ID_AA64MMFR3_EL1_Type_MEC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _update_ID_AA64MMFR3_EL1_Type_MEC (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


end ArmFull.Functions
