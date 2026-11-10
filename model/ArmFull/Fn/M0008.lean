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

def _get_SPSR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SPSR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SPSR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SPSR_abt_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SPSR_fiq_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SPSR_hyp_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_SPSR_irq_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_SPSR_mon_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_SPSR_svc_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_SPSR_und_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_TCR2_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_TCR2_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_TCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_TCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_TCR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_TFSRE0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_TFSR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_TFSR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_TFSR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_TLBTR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_TRFCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_TRFCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_TRFCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_TTBCR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_TTBCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_TTBR0_EL1_Type_bits (v : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((128 -i 1))) 0)


def _get_TTBR0_EL2_Type_bits (v : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((128 -i 1))) 0)


def _get_TTBR0_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_TTBR0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_TTBR1_EL1_Type_bits (v : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((128 -i 1))) 0)


def _get_TTBR1_EL2_Type_bits (v : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((128 -i 1))) 0)


def _get_TTBR1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_VDFSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_VDISR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_VDISR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_VMECID_A_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_VMECID_P_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_VMPIDR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_VMPIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_VNCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_VPIDR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_VPIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_VSESR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_VSTCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_VSTTBR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_VTCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_VTCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _get_VTTBR_EL2_Type_bits (v : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((128 -i 1))) 0)


def _get_VTTBR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ZCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ZCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_ZCR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((64 -i 1))) 0)


def _get_Configuration_Type_CFGEND (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_Configuration_Type_CFGEND (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_Configuration_Type_CONFIG64 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _update_Configuration_Type_CONFIG64 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _get_Configuration_Type_CfgNMFI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)


def _update_Configuration_Type_CfgNMFI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)


def _get_Configuration_Type_Cp15SDisable (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def _update_Configuration_Type_Cp15SDisable (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def _get_Configuration_Type_Cp15SDisable2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)


def _update_Configuration_Type_Cp15SDisable2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)


def _get_Configuration_Type_ExceptInit (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _update_Configuration_Type_ExceptInit (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _get_Configuration_Type_HIVECS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_Configuration_Type_HIVECS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_Configuration_Type_RW (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_Configuration_Type_RW (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_EDSCR_Type_RW (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 10 x)


def _update_HCR_EL2_Type_RW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_SCRType_RW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _update_SCR_EL3_Type_RW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _get_EDSCR_Type_RW (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 13 10)


def _get_HCR_EL2_Type_RW (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_SCRType_RW (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _get_SCR_EL3_Type_RW (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _get_Configuration_Type_disableNIDebug (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _update_Configuration_Type_disableNIDebug (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _get_Configuration_Type_disableSPIDebug (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)


def _update_Configuration_Type_disableSPIDebug (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)


def _get_Configuration_Type_disableSPNIDebug (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)


def _update_Configuration_Type_disableSPNIDebug (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)


def undefined_DormantCtl_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_DormantCtl_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_DormantCtl_Type_Dbgnopwrdwn (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_DormantCtl_Type_Dbgnopwrdwn (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_DormantCtl_Type_PowerDownStatusSupport (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _update_DormantCtl_Type_PowerDownStatusSupport (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_DormantCtl_Type_ResetCatchStatus (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _update_DormantCtl_Type_ResetCatchStatus (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _get_DormantCtl_Type_TestResetCatch (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _update_DormantCtl_Type_TestResetCatch (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _get_DormantCtl_Type_dbgpwrupreq (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)


def _update_DormantCtl_Type_dbgpwrupreq (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _get_DormantCtl_Type_dbgrstreq (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _update_DormantCtl_Type_dbgrstreq (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _get_DormantCtl_Type_etmpwrdwnreq (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)


def _update_DormantCtl_Type_etmpwrdwnreq (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)


def _get_DormantCtl_Type_etmpwrupreq (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _update_DormantCtl_Type_etmpwrupreq (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _get_DormantCtl_Type_nDbgpwrdwnreq (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_DormantCtl_Type_nDbgpwrdwnreq (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_DormantCtl_Type_nPU (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_DormantCtl_Type_nPU (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_DormantCtl_Type_standbywfe (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _update_DormantCtl_Type_standbywfe (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _get_DormantCtl_Type_standbywfi (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_DormantCtl_Type_standbywfi (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def undefined_Feature (ℓ : ChoiceLabel) (_ : Unit) : SailM Feature := do
  (internal_pick_at (ℓ.child 0)
    [FEAT_AA32EL0, FEAT_AA32EL1, FEAT_AA32EL2, FEAT_AA32EL3, FEAT_AA64EL0, FEAT_AA64EL1, FEAT_AA64EL2, FEAT_AA64EL3, FEAT_EL0, FEAT_EL1, FEAT_EL2, FEAT_EL3, FEAT_AES, FEAT_AdvSIMD, FEAT_CSV2_1p1, FEAT_CSV2_1p2, FEAT_CSV2_2, FEAT_CSV2_3, FEAT_DoubleLock, FEAT_ETMv4, FEAT_ETMv4p1, FEAT_ETMv4p2, FEAT_ETMv4p3, FEAT_ETMv4p4, FEAT_ETMv4p5, FEAT_ETMv4p6, FEAT_ETS2, FEAT_FP, FEAT_GICv3, FEAT_GICv3_LEGACY, FEAT_GICv3_TDIR, FEAT_GICv3p1, FEAT_GICv4, FEAT_GICv4p1, FEAT_IVIPT, FEAT_PCSRv8, FEAT_PMULL, FEAT_PMUv3, FEAT_PMUv3_EXT, FEAT_PMUv3_EXT32, FEAT_SHA1, FEAT_SHA256, FEAT_TRC_EXT, FEAT_TRC_SR, FEAT_nTLBPA, FEAT_CRC32, FEAT_Debugv8p1, FEAT_HAFDBS, FEAT_HPDS, FEAT_LOR, FEAT_LSE, FEAT_PAN, FEAT_PMUv3p1, FEAT_RDM, FEAT_VHE, FEAT_VMID16, FEAT_AA32BF16, FEAT_AA32HPD, FEAT_AA32I8MM, FEAT_ASMv8p2, FEAT_DPB, FEAT_Debugv8p2, FEAT_EDHSR, FEAT_F32MM, FEAT_F64MM, FEAT_FP16, FEAT_HPDS2, FEAT_I8MM, FEAT_IESB, FEAT_LPA, FEAT_LSMAOC, FEAT_LVA, FEAT_MPAM, FEAT_PAN2, FEAT_PCSRv8p2, FEAT_RAS, FEAT_SHA3, FEAT_SHA512, FEAT_SM3, FEAT_SM4, FEAT_SPE, FEAT_SVE, FEAT_TTCNP, FEAT_UAO, FEAT_VPIPT, FEAT_XNX, FEAT_CCIDX, FEAT_CONSTPACFIELD, FEAT_EPAC, FEAT_FCMA, FEAT_FPAC, FEAT_FPACCOMBINE, FEAT_JSCVT, FEAT_LRCPC, FEAT_NV, FEAT_PACIMP, FEAT_PACQARMA3, FEAT_PACQARMA5, FEAT_PAuth, FEAT_SPEv1p1, FEAT_AMUv1, FEAT_BBM, FEAT_CNTSC, FEAT_DIT, FEAT_Debugv8p4, FEAT_DotProd, FEAT_DoubleFault, FEAT_FHM, FEAT_FlagM, FEAT_IDST, FEAT_LRCPC2, FEAT_LSE2, FEAT_NV2, FEAT_PMUv3p4, FEAT_RASSAv1p1, FEAT_RASv1p1, FEAT_S2FWB, FEAT_SEL2, FEAT_TLBIOS, FEAT_TLBIRANGE, FEAT_TRF, FEAT_TTL, FEAT_TTST, FEAT_BTI, FEAT_CSV2, FEAT_CSV3, FEAT_DPB2, FEAT_E0PD, FEAT_EVT, FEAT_ExS, FEAT_FRINTTS, FEAT_FlagM2, FEAT_GTG, FEAT_MTE, FEAT_MTE2, FEAT_PMUv3p5, FEAT_RNG, FEAT_RNG_TRAP, FEAT_SB, FEAT_SPECRES, FEAT_SSBS, FEAT_SSBS2, FEAT_AMUv1p1, FEAT_BF16, FEAT_DGH, FEAT_ECV, FEAT_FGT, FEAT_HPMN0, FEAT_MPAMv0p1, FEAT_MPAMv1p1, FEAT_MTPMU, FEAT_PAuth2, FEAT_TWED, FEAT_AFP, FEAT_EBF16, FEAT_HCX, FEAT_LPA2, FEAT_LS64, FEAT_LS64_ACCDATA, FEAT_LS64_V, FEAT_MTE3, FEAT_PAN3, FEAT_PMUv3p7, FEAT_RPRES, FEAT_SPEv1p2, FEAT_WFxT, FEAT_XS, FEAT_CMOW, FEAT_Debugv8p8, FEAT_GICv3_NMI, FEAT_HBC, FEAT_MOPS, FEAT_NMI, FEAT_PMUv3_EXT64, FEAT_PMUv3_TH, FEAT_PMUv3p8, FEAT_SCTLR2, FEAT_SPEv1p3, FEAT_TCR2, FEAT_TIDCP1, FEAT_ADERR, FEAT_AIE, FEAT_ANERR, FEAT_CLRBHB, FEAT_CSSC, FEAT_Debugv8p9, FEAT_DoubleFault2, FEAT_ECBHB, FEAT_FGT2, FEAT_HAFT, FEAT_LRCPC3, FEAT_MTE4, FEAT_MTE_ASYM_FAULT, FEAT_MTE_ASYNC, FEAT_MTE_CANONICAL_TAGS, FEAT_MTE_NO_ADDRESS_TAGS, FEAT_MTE_PERM, FEAT_MTE_STORE_ONLY, FEAT_MTE_TAGGED_FAR, FEAT_PCSRv8p9, FEAT_PFAR, FEAT_PMUv3_EDGE, FEAT_PMUv3_ICNTR, FEAT_PMUv3_SS, FEAT_PMUv3p9, FEAT_PRFMSLC, FEAT_RASSAv2, FEAT_RASv2, FEAT_RPRFM, FEAT_S1PIE, FEAT_S1POE, FEAT_S2PIE, FEAT_S2POE, FEAT_SPECRES2, FEAT_SPE_CRR, FEAT_SPE_FDS, FEAT_SPEv1p4, FEAT_SPMU, FEAT_THE, FEAT_DoPD, FEAT_ETE, FEAT_SVE2, FEAT_SVE_AES, FEAT_SVE_BitPerm, FEAT_SVE_PMULL128, FEAT_SVE_SHA3, FEAT_SVE_SM4, FEAT_TME, FEAT_TRBE, FEAT_ETEv1p1, FEAT_BRBE, FEAT_ETEv1p2, FEAT_RME, FEAT_SME, FEAT_SME_F64F64, FEAT_SME_FA64, FEAT_SME_I16I64, FEAT_BRBEv1p1, FEAT_MEC, FEAT_SME2, FEAT_ABLE, FEAT_CHK, FEAT_D128, FEAT_EBEP, FEAT_ETEv1p3, FEAT_GCS, FEAT_ITE, FEAT_LSE128, FEAT_LVA3, FEAT_SEBEP, FEAT_SME2p1, FEAT_SME_F16F16, FEAT_SVE2p1, FEAT_SVE_B16B16, FEAT_SYSINSTR128, FEAT_SYSREG128, FEAT_TRBE_EXT, FEAT_TRBE_MPAM])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 257 -/
def Feature_of_num (arg_ : Nat) : Feature :=
  match arg_ with
  | 0 => FEAT_AA32EL0
  | 1 => FEAT_AA32EL1
  | 2 => FEAT_AA32EL2
  | 3 => FEAT_AA32EL3
  | 4 => FEAT_AA64EL0
  | 5 => FEAT_AA64EL1
  | 6 => FEAT_AA64EL2
  | 7 => FEAT_AA64EL3
  | 8 => FEAT_EL0
  | 9 => FEAT_EL1
  | 10 => FEAT_EL2
  | 11 => FEAT_EL3
  | 12 => FEAT_AES
  | 13 => FEAT_AdvSIMD
  | 14 => FEAT_CSV2_1p1
  | 15 => FEAT_CSV2_1p2
  | 16 => FEAT_CSV2_2
  | 17 => FEAT_CSV2_3
  | 18 => FEAT_DoubleLock
  | 19 => FEAT_ETMv4
  | 20 => FEAT_ETMv4p1
  | 21 => FEAT_ETMv4p2
  | 22 => FEAT_ETMv4p3
  | 23 => FEAT_ETMv4p4
  | 24 => FEAT_ETMv4p5
  | 25 => FEAT_ETMv4p6
  | 26 => FEAT_ETS2
  | 27 => FEAT_FP
  | 28 => FEAT_GICv3
  | 29 => FEAT_GICv3_LEGACY
  | 30 => FEAT_GICv3_TDIR
  | 31 => FEAT_GICv3p1
  | 32 => FEAT_GICv4
  | 33 => FEAT_GICv4p1
  | 34 => FEAT_IVIPT
  | 35 => FEAT_PCSRv8
  | 36 => FEAT_PMULL
  | 37 => FEAT_PMUv3
  | 38 => FEAT_PMUv3_EXT
  | 39 => FEAT_PMUv3_EXT32
  | 40 => FEAT_SHA1
  | 41 => FEAT_SHA256
  | 42 => FEAT_TRC_EXT
  | 43 => FEAT_TRC_SR
  | 44 => FEAT_nTLBPA
  | 45 => FEAT_CRC32
  | 46 => FEAT_Debugv8p1
  | 47 => FEAT_HAFDBS
  | 48 => FEAT_HPDS
  | 49 => FEAT_LOR
  | 50 => FEAT_LSE
  | 51 => FEAT_PAN
  | 52 => FEAT_PMUv3p1
  | 53 => FEAT_RDM
  | 54 => FEAT_VHE
  | 55 => FEAT_VMID16
  | 56 => FEAT_AA32BF16
  | 57 => FEAT_AA32HPD
  | 58 => FEAT_AA32I8MM
  | 59 => FEAT_ASMv8p2
  | 60 => FEAT_DPB
  | 61 => FEAT_Debugv8p2
  | 62 => FEAT_EDHSR
  | 63 => FEAT_F32MM
  | 64 => FEAT_F64MM
  | 65 => FEAT_FP16
  | 66 => FEAT_HPDS2
  | 67 => FEAT_I8MM
  | 68 => FEAT_IESB
  | 69 => FEAT_LPA
  | 70 => FEAT_LSMAOC
  | 71 => FEAT_LVA
  | 72 => FEAT_MPAM
  | 73 => FEAT_PAN2
  | 74 => FEAT_PCSRv8p2
  | 75 => FEAT_RAS
  | 76 => FEAT_SHA3
  | 77 => FEAT_SHA512
  | 78 => FEAT_SM3
  | 79 => FEAT_SM4
  | 80 => FEAT_SPE
  | 81 => FEAT_SVE
  | 82 => FEAT_TTCNP
  | 83 => FEAT_UAO
  | 84 => FEAT_VPIPT
  | 85 => FEAT_XNX
  | 86 => FEAT_CCIDX
  | 87 => FEAT_CONSTPACFIELD
  | 88 => FEAT_EPAC
  | 89 => FEAT_FCMA
  | 90 => FEAT_FPAC
  | 91 => FEAT_FPACCOMBINE
  | 92 => FEAT_JSCVT
  | 93 => FEAT_LRCPC
  | 94 => FEAT_NV
  | 95 => FEAT_PACIMP
  | 96 => FEAT_PACQARMA3
  | 97 => FEAT_PACQARMA5
  | 98 => FEAT_PAuth
  | 99 => FEAT_SPEv1p1
  | 100 => FEAT_AMUv1
  | 101 => FEAT_BBM
  | 102 => FEAT_CNTSC
  | 103 => FEAT_DIT
  | 104 => FEAT_Debugv8p4
  | 105 => FEAT_DotProd
  | 106 => FEAT_DoubleFault
  | 107 => FEAT_FHM
  | 108 => FEAT_FlagM
  | 109 => FEAT_IDST
  | 110 => FEAT_LRCPC2
  | 111 => FEAT_LSE2
  | 112 => FEAT_NV2
  | 113 => FEAT_PMUv3p4
  | 114 => FEAT_RASSAv1p1
  | 115 => FEAT_RASv1p1
  | 116 => FEAT_S2FWB
  | 117 => FEAT_SEL2
  | 118 => FEAT_TLBIOS
  | 119 => FEAT_TLBIRANGE
  | 120 => FEAT_TRF
  | 121 => FEAT_TTL
  | 122 => FEAT_TTST
  | 123 => FEAT_BTI
  | 124 => FEAT_CSV2
  | 125 => FEAT_CSV3
  | 126 => FEAT_DPB2
  | 127 => FEAT_E0PD
  | 128 => FEAT_EVT
  | 129 => FEAT_ExS
  | 130 => FEAT_FRINTTS
  | 131 => FEAT_FlagM2
  | 132 => FEAT_GTG
  | 133 => FEAT_MTE
  | 134 => FEAT_MTE2
  | 135 => FEAT_PMUv3p5
  | 136 => FEAT_RNG
  | 137 => FEAT_RNG_TRAP
  | 138 => FEAT_SB
  | 139 => FEAT_SPECRES
  | 140 => FEAT_SSBS
  | 141 => FEAT_SSBS2
  | 142 => FEAT_AMUv1p1
  | 143 => FEAT_BF16
  | 144 => FEAT_DGH
  | 145 => FEAT_ECV
  | 146 => FEAT_FGT
  | 147 => FEAT_HPMN0
  | 148 => FEAT_MPAMv0p1
  | 149 => FEAT_MPAMv1p1
  | 150 => FEAT_MTPMU
  | 151 => FEAT_PAuth2
  | 152 => FEAT_TWED
  | 153 => FEAT_AFP
  | 154 => FEAT_EBF16
  | 155 => FEAT_HCX
  | 156 => FEAT_LPA2
  | 157 => FEAT_LS64
  | 158 => FEAT_LS64_ACCDATA
  | 159 => FEAT_LS64_V
  | 160 => FEAT_MTE3
  | 161 => FEAT_PAN3
  | 162 => FEAT_PMUv3p7
  | 163 => FEAT_RPRES
  | 164 => FEAT_SPEv1p2
  | 165 => FEAT_WFxT
  | 166 => FEAT_XS
  | 167 => FEAT_CMOW
  | 168 => FEAT_Debugv8p8
  | 169 => FEAT_GICv3_NMI
  | 170 => FEAT_HBC
  | 171 => FEAT_MOPS
  | 172 => FEAT_NMI
  | 173 => FEAT_PMUv3_EXT64
  | 174 => FEAT_PMUv3_TH
  | 175 => FEAT_PMUv3p8
  | 176 => FEAT_SCTLR2
  | 177 => FEAT_SPEv1p3
  | 178 => FEAT_TCR2
  | 179 => FEAT_TIDCP1
  | 180 => FEAT_ADERR
  | 181 => FEAT_AIE
  | 182 => FEAT_ANERR
  | 183 => FEAT_CLRBHB
  | 184 => FEAT_CSSC
  | 185 => FEAT_Debugv8p9
  | 186 => FEAT_DoubleFault2
  | 187 => FEAT_ECBHB
  | 188 => FEAT_FGT2
  | 189 => FEAT_HAFT
  | 190 => FEAT_LRCPC3
  | 191 => FEAT_MTE4
  | 192 => FEAT_MTE_ASYM_FAULT
  | 193 => FEAT_MTE_ASYNC
  | 194 => FEAT_MTE_CANONICAL_TAGS
  | 195 => FEAT_MTE_NO_ADDRESS_TAGS
  | 196 => FEAT_MTE_PERM
  | 197 => FEAT_MTE_STORE_ONLY
  | 198 => FEAT_MTE_TAGGED_FAR
  | 199 => FEAT_PCSRv8p9
  | 200 => FEAT_PFAR
  | 201 => FEAT_PMUv3_EDGE
  | 202 => FEAT_PMUv3_ICNTR
  | 203 => FEAT_PMUv3_SS
  | 204 => FEAT_PMUv3p9
  | 205 => FEAT_PRFMSLC
  | 206 => FEAT_RASSAv2
  | 207 => FEAT_RASv2
  | 208 => FEAT_RPRFM
  | 209 => FEAT_S1PIE
  | 210 => FEAT_S1POE
  | 211 => FEAT_S2PIE
  | 212 => FEAT_S2POE
  | 213 => FEAT_SPECRES2
  | 214 => FEAT_SPE_CRR
  | 215 => FEAT_SPE_FDS
  | 216 => FEAT_SPEv1p4
  | 217 => FEAT_SPMU
  | 218 => FEAT_THE
  | 219 => FEAT_DoPD
  | 220 => FEAT_ETE
  | 221 => FEAT_SVE2
  | 222 => FEAT_SVE_AES
  | 223 => FEAT_SVE_BitPerm
  | 224 => FEAT_SVE_PMULL128
  | 225 => FEAT_SVE_SHA3
  | 226 => FEAT_SVE_SM4
  | 227 => FEAT_TME
  | 228 => FEAT_TRBE
  | 229 => FEAT_ETEv1p1
  | 230 => FEAT_BRBE
  | 231 => FEAT_ETEv1p2
  | 232 => FEAT_RME
  | 233 => FEAT_SME
  | 234 => FEAT_SME_F64F64
  | 235 => FEAT_SME_FA64
  | 236 => FEAT_SME_I16I64
  | 237 => FEAT_BRBEv1p1
  | 238 => FEAT_MEC
  | 239 => FEAT_SME2
  | 240 => FEAT_ABLE
  | 241 => FEAT_CHK
  | 242 => FEAT_D128
  | 243 => FEAT_EBEP
  | 244 => FEAT_ETEv1p3
  | 245 => FEAT_GCS
  | 246 => FEAT_ITE
  | 247 => FEAT_LSE128
  | 248 => FEAT_LVA3
  | 249 => FEAT_SEBEP
  | 250 => FEAT_SME2p1
  | 251 => FEAT_SME_F16F16
  | 252 => FEAT_SVE2p1
  | 253 => FEAT_SVE_B16B16
  | 254 => FEAT_SYSINSTR128
  | 255 => FEAT_SYSREG128
  | 256 => FEAT_TRBE_EXT
  | _ => FEAT_TRBE_MPAM


def num_of_Feature (arg_ : Feature) : Int :=
  match arg_ with
  | .FEAT_AA32EL0 => 0
  | .FEAT_AA32EL1 => 1
  | .FEAT_AA32EL2 => 2
  | .FEAT_AA32EL3 => 3
  | .FEAT_AA64EL0 => 4
  | .FEAT_AA64EL1 => 5
  | .FEAT_AA64EL2 => 6
  | .FEAT_AA64EL3 => 7
  | .FEAT_EL0 => 8
  | .FEAT_EL1 => 9
  | .FEAT_EL2 => 10
  | .FEAT_EL3 => 11
  | .FEAT_AES => 12
  | .FEAT_AdvSIMD => 13
  | .FEAT_CSV2_1p1 => 14
  | .FEAT_CSV2_1p2 => 15
  | .FEAT_CSV2_2 => 16
  | .FEAT_CSV2_3 => 17
  | .FEAT_DoubleLock => 18
  | .FEAT_ETMv4 => 19
  | .FEAT_ETMv4p1 => 20
  | .FEAT_ETMv4p2 => 21
  | .FEAT_ETMv4p3 => 22
  | .FEAT_ETMv4p4 => 23
  | .FEAT_ETMv4p5 => 24
  | .FEAT_ETMv4p6 => 25
  | .FEAT_ETS2 => 26
  | .FEAT_FP => 27
  | .FEAT_GICv3 => 28
  | .FEAT_GICv3_LEGACY => 29
  | .FEAT_GICv3_TDIR => 30
  | .FEAT_GICv3p1 => 31
  | .FEAT_GICv4 => 32
  | .FEAT_GICv4p1 => 33
  | .FEAT_IVIPT => 34
  | .FEAT_PCSRv8 => 35
  | .FEAT_PMULL => 36
  | .FEAT_PMUv3 => 37
  | .FEAT_PMUv3_EXT => 38
  | .FEAT_PMUv3_EXT32 => 39
  | .FEAT_SHA1 => 40
  | .FEAT_SHA256 => 41
  | .FEAT_TRC_EXT => 42
  | .FEAT_TRC_SR => 43
  | .FEAT_nTLBPA => 44
  | .FEAT_CRC32 => 45
  | .FEAT_Debugv8p1 => 46
  | .FEAT_HAFDBS => 47
  | .FEAT_HPDS => 48
  | .FEAT_LOR => 49
  | .FEAT_LSE => 50
  | .FEAT_PAN => 51
  | .FEAT_PMUv3p1 => 52
  | .FEAT_RDM => 53
  | .FEAT_VHE => 54
  | .FEAT_VMID16 => 55
  | .FEAT_AA32BF16 => 56
  | .FEAT_AA32HPD => 57
  | .FEAT_AA32I8MM => 58
  | .FEAT_ASMv8p2 => 59
  | .FEAT_DPB => 60
  | .FEAT_Debugv8p2 => 61
  | .FEAT_EDHSR => 62
  | .FEAT_F32MM => 63
  | .FEAT_F64MM => 64
  | .FEAT_FP16 => 65
  | .FEAT_HPDS2 => 66
  | .FEAT_I8MM => 67
  | .FEAT_IESB => 68
  | .FEAT_LPA => 69
  | .FEAT_LSMAOC => 70
  | .FEAT_LVA => 71
  | .FEAT_MPAM => 72
  | .FEAT_PAN2 => 73
  | .FEAT_PCSRv8p2 => 74
  | .FEAT_RAS => 75
  | .FEAT_SHA3 => 76
  | .FEAT_SHA512 => 77
  | .FEAT_SM3 => 78
  | .FEAT_SM4 => 79
  | .FEAT_SPE => 80
  | .FEAT_SVE => 81
  | .FEAT_TTCNP => 82
  | .FEAT_UAO => 83
  | .FEAT_VPIPT => 84
  | .FEAT_XNX => 85
  | .FEAT_CCIDX => 86
  | .FEAT_CONSTPACFIELD => 87
  | .FEAT_EPAC => 88
  | .FEAT_FCMA => 89
  | .FEAT_FPAC => 90
  | .FEAT_FPACCOMBINE => 91
  | .FEAT_JSCVT => 92
  | .FEAT_LRCPC => 93
  | .FEAT_NV => 94
  | .FEAT_PACIMP => 95
  | .FEAT_PACQARMA3 => 96
  | .FEAT_PACQARMA5 => 97
  | .FEAT_PAuth => 98
  | .FEAT_SPEv1p1 => 99
  | .FEAT_AMUv1 => 100
  | .FEAT_BBM => 101
  | .FEAT_CNTSC => 102
  | .FEAT_DIT => 103
  | .FEAT_Debugv8p4 => 104
  | .FEAT_DotProd => 105
  | .FEAT_DoubleFault => 106
  | .FEAT_FHM => 107
  | .FEAT_FlagM => 108
  | .FEAT_IDST => 109
  | .FEAT_LRCPC2 => 110
  | .FEAT_LSE2 => 111
  | .FEAT_NV2 => 112
  | .FEAT_PMUv3p4 => 113
  | .FEAT_RASSAv1p1 => 114
  | .FEAT_RASv1p1 => 115
  | .FEAT_S2FWB => 116
  | .FEAT_SEL2 => 117
  | .FEAT_TLBIOS => 118
  | .FEAT_TLBIRANGE => 119
  | .FEAT_TRF => 120
  | .FEAT_TTL => 121
  | .FEAT_TTST => 122
  | .FEAT_BTI => 123
  | .FEAT_CSV2 => 124
  | .FEAT_CSV3 => 125
  | .FEAT_DPB2 => 126
  | .FEAT_E0PD => 127
  | .FEAT_EVT => 128
  | .FEAT_ExS => 129
  | .FEAT_FRINTTS => 130
  | .FEAT_FlagM2 => 131
  | .FEAT_GTG => 132
  | .FEAT_MTE => 133
  | .FEAT_MTE2 => 134
  | .FEAT_PMUv3p5 => 135
  | .FEAT_RNG => 136
  | .FEAT_RNG_TRAP => 137
  | .FEAT_SB => 138
  | .FEAT_SPECRES => 139
  | .FEAT_SSBS => 140
  | .FEAT_SSBS2 => 141
  | .FEAT_AMUv1p1 => 142
  | .FEAT_BF16 => 143
  | .FEAT_DGH => 144
  | .FEAT_ECV => 145
  | .FEAT_FGT => 146
  | .FEAT_HPMN0 => 147
  | .FEAT_MPAMv0p1 => 148
  | .FEAT_MPAMv1p1 => 149
  | .FEAT_MTPMU => 150
  | .FEAT_PAuth2 => 151
  | .FEAT_TWED => 152
  | .FEAT_AFP => 153
  | .FEAT_EBF16 => 154
  | .FEAT_HCX => 155
  | .FEAT_LPA2 => 156
  | .FEAT_LS64 => 157
  | .FEAT_LS64_ACCDATA => 158
  | .FEAT_LS64_V => 159
  | .FEAT_MTE3 => 160
  | .FEAT_PAN3 => 161
  | .FEAT_PMUv3p7 => 162
  | .FEAT_RPRES => 163
  | .FEAT_SPEv1p2 => 164
  | .FEAT_WFxT => 165
  | .FEAT_XS => 166
  | .FEAT_CMOW => 167
  | .FEAT_Debugv8p8 => 168
  | .FEAT_GICv3_NMI => 169
  | .FEAT_HBC => 170
  | .FEAT_MOPS => 171
  | .FEAT_NMI => 172
  | .FEAT_PMUv3_EXT64 => 173
  | .FEAT_PMUv3_TH => 174
  | .FEAT_PMUv3p8 => 175
  | .FEAT_SCTLR2 => 176
  | .FEAT_SPEv1p3 => 177
  | .FEAT_TCR2 => 178
  | .FEAT_TIDCP1 => 179
  | .FEAT_ADERR => 180
  | .FEAT_AIE => 181
  | .FEAT_ANERR => 182
  | .FEAT_CLRBHB => 183
  | .FEAT_CSSC => 184
  | .FEAT_Debugv8p9 => 185
  | .FEAT_DoubleFault2 => 186
  | .FEAT_ECBHB => 187
  | .FEAT_FGT2 => 188
  | .FEAT_HAFT => 189
  | .FEAT_LRCPC3 => 190
  | .FEAT_MTE4 => 191
  | .FEAT_MTE_ASYM_FAULT => 192
  | .FEAT_MTE_ASYNC => 193
  | .FEAT_MTE_CANONICAL_TAGS => 194
  | .FEAT_MTE_NO_ADDRESS_TAGS => 195
  | .FEAT_MTE_PERM => 196
  | .FEAT_MTE_STORE_ONLY => 197
  | .FEAT_MTE_TAGGED_FAR => 198
  | .FEAT_PCSRv8p9 => 199
  | .FEAT_PFAR => 200
  | .FEAT_PMUv3_EDGE => 201
  | .FEAT_PMUv3_ICNTR => 202
  | .FEAT_PMUv3_SS => 203
  | .FEAT_PMUv3p9 => 204
  | .FEAT_PRFMSLC => 205
  | .FEAT_RASSAv2 => 206
  | .FEAT_RASv2 => 207
  | .FEAT_RPRFM => 208
  | .FEAT_S1PIE => 209
  | .FEAT_S1POE => 210
  | .FEAT_S2PIE => 211
  | .FEAT_S2POE => 212
  | .FEAT_SPECRES2 => 213
  | .FEAT_SPE_CRR => 214
  | .FEAT_SPE_FDS => 215
  | .FEAT_SPEv1p4 => 216
  | .FEAT_SPMU => 217
  | .FEAT_THE => 218
  | .FEAT_DoPD => 219
  | .FEAT_ETE => 220
  | .FEAT_SVE2 => 221
  | .FEAT_SVE_AES => 222
  | .FEAT_SVE_BitPerm => 223
  | .FEAT_SVE_PMULL128 => 224
  | .FEAT_SVE_SHA3 => 225
  | .FEAT_SVE_SM4 => 226
  | .FEAT_TME => 227
  | .FEAT_TRBE => 228
  | .FEAT_ETEv1p1 => 229
  | .FEAT_BRBE => 230
  | .FEAT_ETEv1p2 => 231
  | .FEAT_RME => 232
  | .FEAT_SME => 233
  | .FEAT_SME_F64F64 => 234
  | .FEAT_SME_FA64 => 235
  | .FEAT_SME_I16I64 => 236
  | .FEAT_BRBEv1p1 => 237
  | .FEAT_MEC => 238
  | .FEAT_SME2 => 239
  | .FEAT_ABLE => 240
  | .FEAT_CHK => 241
  | .FEAT_D128 => 242
  | .FEAT_EBEP => 243
  | .FEAT_ETEv1p3 => 244
  | .FEAT_GCS => 245
  | .FEAT_ITE => 246
  | .FEAT_LSE128 => 247
  | .FEAT_LVA3 => 248
  | .FEAT_SEBEP => 249
  | .FEAT_SME2p1 => 250
  | .FEAT_SME_F16F16 => 251
  | .FEAT_SVE2p1 => 252
  | .FEAT_SVE_B16B16 => 253
  | .FEAT_SYSINSTR128 => 254
  | .FEAT_SYSREG128 => 255
  | .FEAT_TRBE_EXT => 256
  | .FEAT_TRBE_MPAM => 257


end ArmFull.Functions
