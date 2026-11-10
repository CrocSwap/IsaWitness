import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0056
import ArmFull.Fn.M0058
import ArmFull.Fn.M0066
import ArmFull.Fn.M0067
import ArmFull.Fn.M0068

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

def _set_HAFGRTR_EL2_Type_AMEVCNTR12_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR12_EL0 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTR12_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR12_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVCNTR13_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR13_EL0 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTR13_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR13_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVCNTR14_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR14_EL0 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTR14_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR14_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVCNTR15_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR15_EL0 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTR15_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR15_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVCNTR16_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR16_EL0 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTR16_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR16_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVCNTR17_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR17_EL0 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTR17_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR17_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVCNTR18_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR18_EL0 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTR18_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR18_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVCNTR19_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVCNTR19_EL0 r v)


def _set_AMCG1IDR_EL0_Type_AMEVCNTR19_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_AMEVCNTR19_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVTYPER10_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER10_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVTYPER110_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER110_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVTYPER111_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER111_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVTYPER112_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER112_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVTYPER113_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER113_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVTYPER114_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER114_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVTYPER115_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER115_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVTYPER11_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER11_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVTYPER12_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER12_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVTYPER13_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER13_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVTYPER14_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER14_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVTYPER15_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER15_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVTYPER16_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER16_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVTYPER17_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER17_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVTYPER18_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER18_EL0 r v)


def _set_HAFGRTR_EL2_Type_AMEVTYPER19_EL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HAFGRTR_EL2_Type_AMEVTYPER19_EL0 r v)


def _set_ID_AA64DFR1_EL1_Type_ABLE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR1_EL1_Type_ABLE r v)


def _set_EDDFR1_Type_ABLE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDDFR1_Type_ABLE r v)


def _set_ID_AA64DFR1_EL1_Type_ABL_CMPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR1_EL1_Type_ABL_CMPs r v)


def _set_EDDFR1_Type_ABL_CMPs (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDDFR1_Type_ABL_CMPs r v)


def _set_ID_AA64DFR1_EL1_Type_DPFZS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR1_EL1_Type_DPFZS r v)


def _set_ID_AA64DFR1_EL1_Type_EBEP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR1_EL1_Type_EBEP r v)


def _set_EDDFR1_Type_EBEP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDDFR1_Type_EBEP r v)


def _set_ID_AA64DFR1_EL1_Type_PMICNTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR1_EL1_Type_PMICNTR r v)


def _set_EDDFR1_Type_PMICNTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDDFR1_Type_PMICNTR r v)


def _set_ID_AA64DFR1_EL1_Type_SPMU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR1_EL1_Type_SPMU r v)


def _set_EDDFR1_Type_SPMU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDDFR1_Type_SPMU r v)


def _set_ID_AA64DFR1_EL1_Type_SYSPMUID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64DFR1_EL1_Type_SYSPMUID r v)


def _set_EDDFR1_Type_SYSPMUID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDDFR1_Type_SYSPMUID r v)


def _set_ACCDATA_EL1_Type_ACCDATA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ACCDATA_EL1_Type_ACCDATA r v)


def _set_PMSSCR_EL1_Type_NC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSSCR_EL1_Type_NC r v)


def _set_LORID_EL1_Type_LR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_LORID_EL1_Type_LR r v)


def _set_CNTP_TVAL_EL0_Type_TimerValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTP_TVAL_EL0_Type_TimerValue r v)


def _set_CNTHPS_TVAL_EL2_Type_TimerValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHPS_TVAL_EL2_Type_TimerValue r v)


def _set_CNTHP_TVAL_EL2_Type_TimerValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHP_TVAL_EL2_Type_TimerValue r v)


def _set_CNTHVS_TVAL_EL2_Type_TimerValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHVS_TVAL_EL2_Type_TimerValue r v)


def _set_CNTHV_TVAL_EL2_Type_TimerValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHV_TVAL_EL2_Type_TimerValue r v)


def _set_CNTPS_TVAL_EL1_Type_TimerValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTPS_TVAL_EL1_Type_TimerValue r v)


def _set_CNTV_TVAL_EL0_Type_TimerValue (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTV_TVAL_EL0_Type_TimerValue r v)


def _set_ID_AA64ISAR1_EL1_Type_APA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_APA r v)


def _set_ID_AA64ISAR1_EL1_Type_BF16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_BF16 r v)


def _set_ID_AA64ZFR0_EL1_Type_BF16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ZFR0_EL1_Type_BF16 r v)


def _set_ID_ISAR6_EL1_Type_BF16 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_ISAR6_EL1_Type_BF16 r v)


def _set_ID_ISAR6_Type_BF16 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_ISAR6_Type_BF16 r v)


def _set_ID_AA64ISAR1_EL1_Type_DGH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_DGH r v)


def _set_ID_AA64ISAR1_EL1_Type_DPB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_DPB r v)


def _set_ID_AA64ISAR1_EL1_Type_FCMA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_FCMA r v)


def _set_ID_AA64ISAR1_EL1_Type_FRINTTS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_FRINTTS r v)


def _set_ID_AA64ISAR1_EL1_Type_GPA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_GPA r v)


def _set_ID_AA64ISAR1_EL1_Type_GPI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_GPI r v)


def _set_ID_AA64ISAR1_EL1_Type_I8MM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_I8MM r v)


def _set_ID_AA64ZFR0_EL1_Type_I8MM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ZFR0_EL1_Type_I8MM r v)


def _set_ID_ISAR6_EL1_Type_I8MM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_ISAR6_EL1_Type_I8MM r v)


def _set_ID_ISAR6_Type_I8MM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_ISAR6_Type_I8MM r v)


def _set_ID_AA64ISAR1_EL1_Type_JSCVT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_JSCVT r v)


def _set_ID_ISAR6_EL1_Type_JSCVT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_ISAR6_EL1_Type_JSCVT r v)


def _set_ID_ISAR6_Type_JSCVT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_ISAR6_Type_JSCVT r v)


def _set_ID_AA64ISAR1_EL1_Type_LRCPC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_LRCPC r v)


def _set_ID_AA64ISAR1_EL1_Type_LS64 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_LS64 r v)


def _set_ID_AA64ISAR1_EL1_Type_SB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_SB r v)


def _set_ID_ISAR6_EL1_Type_SB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_ISAR6_EL1_Type_SB r v)


def _set_ID_ISAR6_Type_SB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_ISAR6_Type_SB r v)


def _set_ID_AA64ISAR1_EL1_Type_SPECRES (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_SPECRES r v)


def _set_ID_ISAR6_EL1_Type_SPECRES (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_ISAR6_EL1_Type_SPECRES r v)


def _set_ID_ISAR6_Type_SPECRES (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ID_ISAR6_Type_SPECRES r v)


def _set_ID_AA64ISAR1_EL1_Type_XS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_XS r v)


def _set_ID_AA64MMFR4_EL1_Type_EIESB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR4_EL1_Type_EIESB r v)


def _set_ICH_EISR_EL2_Type_Status0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status0 r v)


def _set_GICH_EISR_Type_Status0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_EISR_Type_Status0 r v)


def _set_GICH_ELRSR_Type_Status0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status0 r v)


def _set_ICH_EISR_Type_Status0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_EISR_Type_Status0 r v)


def _set_ICH_ELRSR_EL2_Type_Status0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status0 r v)


def _set_ICH_ELRSR_Type_Status0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status0 r v)


def _set_ICH_EISR_EL2_Type_Status1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status1 r v)


def _set_GICH_EISR_Type_Status1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_EISR_Type_Status1 r v)


def _set_GICH_ELRSR_Type_Status1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status1 r v)


def _set_ICH_EISR_Type_Status1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_EISR_Type_Status1 r v)


def _set_ICH_ELRSR_EL2_Type_Status1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status1 r v)


def _set_ICH_ELRSR_Type_Status1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status1 r v)


def _set_ICH_EISR_EL2_Type_Status10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status10 r v)


def _set_GICH_EISR_Type_Status10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_EISR_Type_Status10 r v)


def _set_GICH_ELRSR_Type_Status10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status10 r v)


def _set_ICH_EISR_Type_Status10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_EISR_Type_Status10 r v)


def _set_ICH_ELRSR_EL2_Type_Status10 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status10 r v)


def _set_ICH_ELRSR_Type_Status10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status10 r v)


def _set_ICH_EISR_EL2_Type_Status11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status11 r v)


def _set_GICH_EISR_Type_Status11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_EISR_Type_Status11 r v)


def _set_GICH_ELRSR_Type_Status11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status11 r v)


def _set_ICH_EISR_Type_Status11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_EISR_Type_Status11 r v)


def _set_ICH_ELRSR_EL2_Type_Status11 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status11 r v)


def _set_ICH_ELRSR_Type_Status11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status11 r v)


def _set_ICH_EISR_EL2_Type_Status12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status12 r v)


def _set_GICH_EISR_Type_Status12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_EISR_Type_Status12 r v)


def _set_GICH_ELRSR_Type_Status12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status12 r v)


def _set_ICH_EISR_Type_Status12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_EISR_Type_Status12 r v)


def _set_ICH_ELRSR_EL2_Type_Status12 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status12 r v)


def _set_ICH_ELRSR_Type_Status12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status12 r v)


def _set_ICH_EISR_EL2_Type_Status13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status13 r v)


def _set_GICH_EISR_Type_Status13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_EISR_Type_Status13 r v)


def _set_GICH_ELRSR_Type_Status13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status13 r v)


def _set_ICH_EISR_Type_Status13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_EISR_Type_Status13 r v)


def _set_ICH_ELRSR_EL2_Type_Status13 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status13 r v)


def _set_ICH_ELRSR_Type_Status13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status13 r v)


def _set_ICH_EISR_EL2_Type_Status14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status14 r v)


def _set_GICH_EISR_Type_Status14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_EISR_Type_Status14 r v)


def _set_GICH_ELRSR_Type_Status14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status14 r v)


def _set_ICH_EISR_Type_Status14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_EISR_Type_Status14 r v)


def _set_ICH_ELRSR_EL2_Type_Status14 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status14 r v)


def _set_ICH_ELRSR_Type_Status14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status14 r v)


def _set_ICH_EISR_EL2_Type_Status15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status15 r v)


def _set_GICH_EISR_Type_Status15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_EISR_Type_Status15 r v)


def _set_GICH_ELRSR_Type_Status15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status15 r v)


def _set_ICH_EISR_Type_Status15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_EISR_Type_Status15 r v)


def _set_ICH_ELRSR_EL2_Type_Status15 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status15 r v)


def _set_ICH_ELRSR_Type_Status15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status15 r v)


def _set_ICH_EISR_EL2_Type_Status2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status2 r v)


def _set_GICH_EISR_Type_Status2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_EISR_Type_Status2 r v)


def _set_GICH_ELRSR_Type_Status2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status2 r v)


def _set_ICH_EISR_Type_Status2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_EISR_Type_Status2 r v)


def _set_ICH_ELRSR_EL2_Type_Status2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status2 r v)


def _set_ICH_ELRSR_Type_Status2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status2 r v)


def _set_ICH_EISR_EL2_Type_Status3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status3 r v)


def _set_GICH_EISR_Type_Status3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_EISR_Type_Status3 r v)


def _set_GICH_ELRSR_Type_Status3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status3 r v)


def _set_ICH_EISR_Type_Status3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_EISR_Type_Status3 r v)


def _set_ICH_ELRSR_EL2_Type_Status3 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status3 r v)


def _set_ICH_ELRSR_Type_Status3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status3 r v)


def _set_ICH_EISR_EL2_Type_Status4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status4 r v)


def _set_GICH_EISR_Type_Status4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_EISR_Type_Status4 r v)


def _set_GICH_ELRSR_Type_Status4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_ELRSR_Type_Status4 r v)


def _set_ICH_EISR_Type_Status4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_EISR_Type_Status4 r v)


def _set_ICH_ELRSR_EL2_Type_Status4 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_ELRSR_EL2_Type_Status4 r v)


def _set_ICH_ELRSR_Type_Status4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_ELRSR_Type_Status4 r v)


def _set_ICH_EISR_EL2_Type_Status5 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_EISR_EL2_Type_Status5 r v)


end ArmFull.Functions
