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

def _get_ID_AA64MMFR3_EL1_Type_S1PIE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _update_ID_AA64MMFR3_EL1_Type_S1PIE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_ID_AA64MMFR3_EL1_Type_S1POE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_ID_AA64MMFR3_EL1_Type_S1POE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_ID_AA64MMFR3_EL1_Type_SCTLRX (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_ID_AA64MMFR3_EL1_Type_SCTLRX (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_ID_AA64MMFR3_EL1_Type_SDERR (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)


def _update_ID_AA64MMFR3_EL1_Type_SDERR (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)


def _get_ID_AA64MMFR3_EL1_Type_SNERR (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)


def _update_ID_AA64MMFR3_EL1_Type_SNERR (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)


def _get_ID_AA64MMFR3_EL1_Type_Spec_FPACC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)


def _update_ID_AA64MMFR3_EL1_Type_Spec_FPACC (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)


def _get_ID_AA64MMFR3_EL1_Type_TCRX (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_ID_AA64MMFR3_EL1_Type_TCRX (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def Mk_ICH_VTR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ICH_VTR_EL2_Type_ListRegs (v : (BitVec 64)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)


def _update_ICH_VTR_EL2_Type_ListRegs (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 0 x)


def _update_GICH_VTR_Type_ListRegs (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 0 x)


def _update_ICH_VTR_Type_ListRegs (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 0 x)


def _get_GICH_VTR_Type_ListRegs (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)


def _get_ICH_VTR_Type_ListRegs (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)


def _get_ICH_VTR_EL2_Type_PREbits (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 28 26)


def _update_ICH_VTR_EL2_Type_PREbits (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 26 x)


def _update_GICH_VTR_Type_PREbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 26 x)


def _update_ICH_VTR_Type_PREbits (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 26 x)


def _get_GICH_VTR_Type_PREbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 28 26)


def _get_ICH_VTR_Type_PREbits (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 28 26)


def _get_ICH_VTR_EL2_Type_TDS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)


def _update_ICH_VTR_EL2_Type_TDS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)


def _update_ICH_VTR_Type_TDS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)


def _get_ICH_VTR_Type_TDS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)


def _get_ICH_VTR_EL2_Type_nV4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def _update_ICH_VTR_EL2_Type_nV4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def _update_ICH_VTR_Type_nV4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def _get_ICH_VTR_Type_nV4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def Mk_ID_PFR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ID_PFR1_EL1_Type_GenTimer (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_ID_PFR1_EL1_Type_GenTimer (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_ID_PFR1_Type_GenTimer (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_ID_PFR1_EL1_Type_MProgMod (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _update_ID_PFR1_EL1_Type_MProgMod (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_ID_PFR1_Type_MProgMod (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _get_ID_PFR1_EL1_Type_ProgMod (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_ID_PFR1_EL1_Type_ProgMod (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_ID_PFR1_Type_ProgMod (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_ID_PFR1_EL1_Type_Sec_frac (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _update_ID_PFR1_EL1_Type_Sec_frac (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _get_ID_PFR1_Type_Sec_frac (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _get_ID_PFR1_EL1_Type_Security (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_ID_PFR1_EL1_Type_Security (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_ID_PFR1_Type_Security (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_ID_PFR1_EL1_Type_Virt_frac (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _update_ID_PFR1_EL1_Type_Virt_frac (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _get_ID_PFR1_Type_Virt_frac (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_ID_PFR1_EL1_Type_Virtualization (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _update_ID_PFR1_EL1_Type_Virtualization (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _get_ID_PFR1_Type_Virtualization (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def Mk_ICV_EOIR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_ID_DFR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_RNDRRS_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_RNDRRS_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_RNDRRS_Type_RNDRRS (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)


def _update_RNDRRS_Type_RNDRRS (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)


def Mk_LORN_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_LORN_EL1_Type_Num (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _update_LORN_EL1_Type_Num (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def Mk_ICV_IGRPEN0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_CCSIDR_EL1_Type_Associativity (v : (BitVec 64)) : (BitVec 21) :=
  (Sail.BitVec.extractLsb v 23 3)


def _update_CCSIDR_EL1_Type_Associativity (v : (BitVec 64)) (x : (BitVec 21)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 3 x)


def _get_CCSIDR_Type_Associativity (v : (BitVec 32)) : (BitVec 21) :=
  (Sail.BitVec.extractLsb v 23 3)


def _get_CCSIDR_EL1_Type_LineSize (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)


def _update_CCSIDR_EL1_Type_LineSize (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 0 x)


def _get_CCSIDR_Type_LineSize (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)


def undefined_SMPRIMAP_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_SMPRIMAP_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_RNDR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_RNDR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_HFGRTR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_HFGRTR_EL2_Type_AIDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_HFGRTR_EL2_Type_AIDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_HFGRTR_EL2_Type_CCSIDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def _update_HFGRTR_EL2_Type_CCSIDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


def _get_HFGRTR_EL2_Type_CLIDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _update_HFGRTR_EL2_Type_CLIDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _get_HFGRTR_EL2_Type_CTR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _update_HFGRTR_EL2_Type_CTR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _get_HFGRTR_EL2_Type_DCZID_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _update_HFGRTR_EL2_Type_DCZID_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _get_HFGRTR_EL2_Type_ERRIDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)


def _update_HFGRTR_EL2_Type_ERRIDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)


def _get_HFGRTR_EL2_Type_ERXFR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 42 42)


def _update_HFGRTR_EL2_Type_ERXFR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 42 x)


def _get_HFGRTR_EL2_Type_ERXPFGF_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 46 46)


def _update_HFGRTR_EL2_Type_ERXPFGF_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 46 x)


def _get_HFGRTR_EL2_Type_ISR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)


def _update_HFGRTR_EL2_Type_ISR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)


def _get_HFGRTR_EL2_Type_LORID_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


def _update_HFGRTR_EL2_Type_LORID_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)


def _get_HFGRTR_EL2_Type_MIDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)


def _update_HFGRTR_EL2_Type_MIDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)


def _get_HFGRTR_EL2_Type_MPIDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)


def _update_HFGRTR_EL2_Type_MPIDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)


def _get_HFGRTR_EL2_Type_REVIDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _update_HFGRTR_EL2_Type_REVIDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def Mk_ID_DFR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _update_ID_DFR0_EL1_Type_CopDbg (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_ID_DFR0_EL1_Type_CopSDbg (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_ID_DFR0_EL1_Type_CopSDbg (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_ID_DFR0_Type_CopSDbg (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_ID_DFR0_EL1_Type_CopTrc (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _update_ID_DFR0_EL1_Type_CopTrc (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _get_ID_DFR0_Type_CopTrc (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _get_ID_DFR0_EL1_Type_MMapDbg (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _update_ID_DFR0_EL1_Type_MMapDbg (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_ID_DFR0_Type_MMapDbg (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _get_ID_DFR0_EL1_Type_MMapTrc (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_ID_DFR0_EL1_Type_MMapTrc (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_ID_DFR0_Type_MMapTrc (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_ID_DFR0_EL1_Type_MProfDbg (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _update_ID_DFR0_EL1_Type_MProfDbg (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _get_ID_DFR0_Type_MProfDbg (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _get_ID_DFR0_EL1_Type_PerfMon (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _update_ID_DFR0_EL1_Type_PerfMon (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _get_ID_DFR0_Type_PerfMon (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def Mk_ICV_IGRPEN1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_PMXEVCNTR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_PMXEVCNTR_EL0_Type_PMEVCNTR (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)


def _update_PMXEVCNTR_EL0_Type_PMEVCNTR (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)


def Mk_HFGWTR2_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_ICC_SGI1R_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_MVFR2_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_MVFR2_EL1_Type_FPMisc (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_MVFR2_EL1_Type_FPMisc (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_MVFR2_Type_FPMisc (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_MVFR2_EL1_Type_SIMDMisc (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_MVFR2_EL1_Type_SIMDMisc (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_MVFR2_Type_SIMDMisc (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def Mk_DBGAUTHSTATUS_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_DBGAUTHSTATUS_EL1_Type_NSID (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)


def _update_DBGAUTHSTATUS_EL1_Type_NSID (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 0 x)


def _update_CTIAUTHSTATUS_Type_NSID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 0 x)


def _update_DBGAUTHSTATUS_Type_NSID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 0 x)


def _update_PMAUTHSTATUS_Type_NSID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 0 x)


def _get_CTIAUTHSTATUS_Type_NSID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)


def _get_DBGAUTHSTATUS_Type_NSID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)


def _get_PMAUTHSTATUS_Type_NSID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)


def _get_DBGAUTHSTATUS_EL1_Type_NSNID (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 3 2)


def _update_DBGAUTHSTATUS_EL1_Type_NSNID (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 2 x)


def _update_CTIAUTHSTATUS_Type_NSNID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 2 x)


def _update_DBGAUTHSTATUS_Type_NSNID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 2 x)


def _update_PMAUTHSTATUS_Type_NSNID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 2 x)


def _get_CTIAUTHSTATUS_Type_NSNID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 3 2)


def _get_DBGAUTHSTATUS_Type_NSNID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 3 2)


def _get_PMAUTHSTATUS_Type_NSNID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 3 2)


def _get_DBGAUTHSTATUS_EL1_Type_RLID (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 13 12)


def _update_DBGAUTHSTATUS_EL1_Type_RLID (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 12 x)


def _update_PMAUTHSTATUS_Type_RLID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 12 x)


def _get_PMAUTHSTATUS_Type_RLID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 13 12)


def _get_DBGAUTHSTATUS_EL1_Type_RLNID (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _update_DBGAUTHSTATUS_EL1_Type_RLNID (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _update_PMAUTHSTATUS_Type_RLNID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _get_PMAUTHSTATUS_Type_RLNID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _get_DBGAUTHSTATUS_EL1_Type_RTID (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)


def _update_DBGAUTHSTATUS_EL1_Type_RTID (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 24 x)


def _update_PMAUTHSTATUS_Type_RTID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 24 x)


def _get_PMAUTHSTATUS_Type_RTID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)


def _get_DBGAUTHSTATUS_EL1_Type_RTNID (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 27 26)


def _update_DBGAUTHSTATUS_EL1_Type_RTNID (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 26 x)


def _update_PMAUTHSTATUS_Type_RTNID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 26 x)


def _get_PMAUTHSTATUS_Type_RTNID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 27 26)


def _get_DBGAUTHSTATUS_EL1_Type_SID (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)


def _update_DBGAUTHSTATUS_EL1_Type_SID (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 4 x)


def _update_DBGAUTHSTATUS_Type_SID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 4 x)


def _update_PMAUTHSTATUS_Type_SID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 4 x)


def _get_DBGAUTHSTATUS_Type_SID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)


def _get_PMAUTHSTATUS_Type_SID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)


def _get_DBGAUTHSTATUS_EL1_Type_SNID (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)


def _update_DBGAUTHSTATUS_EL1_Type_SNID (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)


def _update_DBGAUTHSTATUS_Type_SNID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 6 x)


def _update_PMAUTHSTATUS_Type_SNID (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 6 x)


def _get_DBGAUTHSTATUS_Type_SNID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)


def _get_PMAUTHSTATUS_Type_SNID (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)


def Mk_ICC_SRE_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_ID_MMFR3_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ID_MMFR3_EL1_Type_BPMaint (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _update_ID_MMFR3_EL1_Type_BPMaint (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_ID_MMFR3_Type_BPMaint (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _get_ID_MMFR3_EL1_Type_CMaintSW (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_ID_MMFR3_EL1_Type_CMaintSW (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_ID_MMFR3_Type_CMaintSW (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_ID_MMFR3_EL1_Type_CMaintVA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_ID_MMFR3_EL1_Type_CMaintVA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_ID_MMFR3_Type_CMaintVA (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_ID_MMFR3_EL1_Type_CMemSz (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _update_ID_MMFR3_EL1_Type_CMemSz (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _get_ID_MMFR3_Type_CMemSz (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_ID_MMFR3_EL1_Type_CohWalk (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _update_ID_MMFR3_EL1_Type_CohWalk (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _get_ID_MMFR3_Type_CohWalk (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _get_ID_MMFR3_EL1_Type_MaintBcst (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


end ArmFull.Functions
