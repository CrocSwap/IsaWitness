import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0050
import ArmFull.Fn.M0064
import ArmFull.Fn.M0084
import ArmFull.Fn.M0085
import ArmFull.Fn.M0086

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

def _set_GITS_STATUSR_Type_WROD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GITS_STATUSR_Type_WROD r v)


def _set_GICM_TYPER_Type_CLR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICM_TYPER_Type_CLR r v)


def _set_GICM_TYPER_Type_NumSPIs (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 11)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICM_TYPER_Type_NumSPIs r v)


def _set_GICD_TYPER2_Type_VID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_TYPER2_Type_VID r v)


def _set_GICD_TYPER2_Type_VIL (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_TYPER2_Type_VIL r v)


def _set_GICD_TYPER2_Type_nASSGIcap (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_TYPER2_Type_nASSGIcap r v)


def _set_GICV_ABPR_Type_Binary_Point (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICV_ABPR_Type_Binary_Point r v)


def _set_GICC_ABPR_Type_Binary_Point (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICC_ABPR_Type_Binary_Point r v)


def _set_GICC_BPR_Type_Binary_Point (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICC_BPR_Type_Binary_Point r v)


def _set_GICV_BPR_Type_Binary_Point (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICV_BPR_Type_Binary_Point r v)


def _set_CTIDEVARCH_Type_ARCHID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTIDEVARCH_Type_ARCHID r v)


def _set_AMDEVARCH_Type_ARCHID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMDEVARCH_Type_ARCHID r v)


def _set_GICR_MPAMIDR_Type_PARTIDmax (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_MPAMIDR_Type_PARTIDmax r v)


def _set_GITS_MPAMIDR_Type_PARTIDmax (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GITS_MPAMIDR_Type_PARTIDmax r v)


def _set_GICR_MPAMIDR_Type_PMGmax (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_MPAMIDR_Type_PMGmax r v)


def _set_GITS_MPAMIDR_Type_PMGmax (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GITS_MPAMIDR_Type_PMGmax r v)


def _set_GICR_CTLR_Type_CES (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_CTLR_Type_CES r v)


def _set_GICR_CTLR_Type_DPG0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_CTLR_Type_DPG0 r v)


def _set_GICR_CTLR_Type_DPG1NS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_CTLR_Type_DPG1NS r v)


def _set_GICR_CTLR_Type_DPG1S (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_CTLR_Type_DPG1S r v)


def _set_GICR_CTLR_Type_EnableLPIs (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_CTLR_Type_EnableLPIs r v)


def _set_GICR_CTLR_Type_UWP (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_CTLR_Type_UWP r v)


def _set_CNTFID0_Type_Frequency (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTFID0_Type_Frequency r v)


def _set_GICD_TYPER_Type_CPUNumber (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_TYPER_Type_CPUNumber r v)


def _set_GICD_TYPER_Type_DVIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_TYPER_Type_DVIS r v)


def _set_GICD_TYPER_Type_ESPI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_TYPER_Type_ESPI r v)


def _set_GICD_TYPER_Type_ESPI_range (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_TYPER_Type_ESPI_range r v)


def _set_GICD_TYPER_Type_ITLinesNumber (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_TYPER_Type_ITLinesNumber r v)


def _set_GICD_TYPER_Type_LPIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_TYPER_Type_LPIS r v)


def _set_GICD_TYPER_Type_MBIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_TYPER_Type_MBIS r v)


def _set_GICD_TYPER_Type_No1N (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_TYPER_Type_No1N r v)


def _set_GICD_TYPER_Type_SecurityExtn (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_TYPER_Type_SecurityExtn r v)


def _set_GICD_TYPER_Type_num_LPIs (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_TYPER_Type_num_LPIs r v)


def _set_CTICIDR0_Type_PRMBL_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTICIDR0_Type_PRMBL_0 r v)


def _set_AMCIDR0_Type_PRMBL_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCIDR0_Type_PRMBL_0 r v)


def _set_EDCIDR0_Type_PRMBL_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDCIDR0_Type_PRMBL_0 r v)


def _set_PMCIDR0_Type_PRMBL_0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMCIDR0_Type_PRMBL_0 r v)


def _set_CTIITCTRL_Type_IME (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTIITCTRL_Type_IME r v)


def _set_EDITCTRL_Type_IME (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDITCTRL_Type_IME r v)


def _set_PMITCTRL_Type_IME (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMITCTRL_Type_IME r v)


def _set_GITS_STATUSR_Type_Overflow (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GITS_STATUSR_Type_Overflow r v)


def _set_GITS_STATUSR_Type_Syndrome (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GITS_STATUSR_Type_Syndrome r v)


def _set_GICC_CTLR_Type_EOImodeS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICC_CTLR_Type_EOImodeS r v)


def _set_GICC_CTLR_Type_FIQBypDisGrp0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICC_CTLR_Type_FIQBypDisGrp0 r v)


def _set_GICC_CTLR_Type_FIQEn (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICC_CTLR_Type_FIQEn r v)


def _set_GICV_CTLR_Type_FIQEn (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICV_CTLR_Type_FIQEn r v)


def _set_GICC_CTLR_Type_IRQBypDisGrp0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICC_CTLR_Type_IRQBypDisGrp0 r v)


def _set_EDPIDR4_Type_DES_2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDPIDR4_Type_DES_2 r v)


def _set_AMPIDR4_Type_DES_2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMPIDR4_Type_DES_2 r v)


def _set_CTIPIDR4_Type_DES_2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTIPIDR4_Type_DES_2 r v)


def _set_PMPIDR4_Type_DES_2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMPIDR4_Type_DES_2 r v)


def _set_CTICONTROL_Type_GLBEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTICONTROL_Type_GLBEN r v)


def _set_GICR_INMIR0_Type_nmi0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi0 r v)


def _set_GICR_INMIR0_Type_nmi1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi1 r v)


def _set_GICR_INMIR0_Type_nmi10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi10 r v)


def _set_GICR_INMIR0_Type_nmi11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi11 r v)


def _set_GICR_INMIR0_Type_nmi12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi12 r v)


def _set_GICR_INMIR0_Type_nmi13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi13 r v)


def _set_GICR_INMIR0_Type_nmi14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi14 r v)


def _set_GICR_INMIR0_Type_nmi15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi15 r v)


def _set_GICR_INMIR0_Type_nmi16 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi16 r v)


def _set_GICR_INMIR0_Type_nmi17 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi17 r v)


def _set_GICR_INMIR0_Type_nmi18 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi18 r v)


def _set_GICR_INMIR0_Type_nmi19 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi19 r v)


def _set_GICR_INMIR0_Type_nmi2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi2 r v)


def _set_GICR_INMIR0_Type_nmi20 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi20 r v)


def _set_GICR_INMIR0_Type_nmi21 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi21 r v)


def _set_GICR_INMIR0_Type_nmi22 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi22 r v)


def _set_GICR_INMIR0_Type_nmi23 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi23 r v)


def _set_GICR_INMIR0_Type_nmi24 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi24 r v)


def _set_GICR_INMIR0_Type_nmi25 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi25 r v)


def _set_GICR_INMIR0_Type_nmi26 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi26 r v)


def _set_GICR_INMIR0_Type_nmi27 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi27 r v)


def _set_GICR_INMIR0_Type_nmi28 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi28 r v)


def _set_GICR_INMIR0_Type_nmi29 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi29 r v)


def _set_GICR_INMIR0_Type_nmi3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi3 r v)


def _set_GICR_INMIR0_Type_nmi30 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi30 r v)


def _set_GICR_INMIR0_Type_nmi31 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi31 r v)


def _set_GICR_INMIR0_Type_nmi4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi4 r v)


def _set_GICR_INMIR0_Type_nmi5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi5 r v)


def _set_GICR_INMIR0_Type_nmi6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi6 r v)


def _set_GICR_INMIR0_Type_nmi7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi7 r v)


def _set_GICR_INMIR0_Type_nmi8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi8 r v)


def _set_GICR_INMIR0_Type_nmi9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_INMIR0_Type_nmi9 r v)


def _set_GICV_CTLR_Type_AckCtl (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICV_CTLR_Type_AckCtl r v)


def _set_GICV_CTLR_Type_EnableGrp1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICV_CTLR_Type_EnableGrp1 r v)


def _set_EDDEVID1_Type_HSR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDDEVID1_Type_HSR r v)


def _set_EDPRCR_Type_COREPURQ (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDPRCR_Type_COREPURQ r v)


def _set_EDPRCR_Type_CWRR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDPRCR_Type_CWRR r v)


def _set_GICR_VSGIPENDR_Type_Busy (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_VSGIPENDR_Type_Busy r v)


def _set_GICR_SYNCR_Type_Busy (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_SYNCR_Type_Busy r v)


def _set_GICR_VSGIPENDR_Type_Pending (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_VSGIPENDR_Type_Pending r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit0 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit1 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit1 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit10 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit10 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit11 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit11 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit12 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit12 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit13 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit13 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit14 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit14 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit15 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit15 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit16 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit16 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit17 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit17 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit18 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit18 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit19 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit19 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit2 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit20 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit20 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit21 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit21 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit22 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit22 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit23 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit23 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit24 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit24 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit25 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit25 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit26 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit26 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit27 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit27 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit28 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit28 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit29 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit29 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit3 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit30 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit30 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit31 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit31 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit4 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit5 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit6 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit7 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit8 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit8 r v)


def _set_GICR_ISENABLER0_Type_Set_enable_bit9 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICR_ISENABLER0_Type_Set_enable_bit9 r v)


def _set_CTICIDR2_Type_PRMBL_2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTICIDR2_Type_PRMBL_2 r v)


def _set_AMCIDR2_Type_PRMBL_2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCIDR2_Type_PRMBL_2 r v)


def _set_EDCIDR2_Type_PRMBL_2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDCIDR2_Type_PRMBL_2 r v)


def _set_PMCIDR2_Type_PRMBL_2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMCIDR2_Type_PRMBL_2 r v)


def _set_EDRCR_Type_CBRRQ (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDRCR_Type_CBRRQ r v)


def _set_EDRCR_Type_CSE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDRCR_Type_CSE r v)


def _set_EDRCR_Type_CSPA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDRCR_Type_CSPA r v)


def _set_EDDEVID_Type_DebugPower (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDDEVID_Type_DebugPower r v)


def _set_GICD_SGIR_Type_CPUTargetList (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_SGIR_Type_CPUTargetList r v)


def _set_GICD_SGIR_Type_NSATT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_SGIR_Type_NSATT r v)


def _set_GICD_SGIR_Type_TargetListFilter (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICD_SGIR_Type_TargetListFilter r v)


def _set_CNTID_Type_CNTSC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTID_Type_CNTSC r v)


def _set_GICH_HCR_Type_EOICount (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICH_HCR_Type_EOICount r v)


def _set_CTIDEVID_Type_EXTMUXNUM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTIDEVID_Type_EXTMUXNUM r v)


def _set_CTIDEVID_Type_INOUT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTIDEVID_Type_INOUT r v)


def _set_CTIDEVID_Type_NUMCHAN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 6)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTIDEVID_Type_NUMCHAN r v)


def _set_CTIDEVID_Type_NUMTRIG (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 6)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTIDEVID_Type_NUMTRIG r v)


def _set_CNTNSAR_Type_NS2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTNSAR_Type_NS2 r v)


def _set_CNTNSAR_Type_NS3 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTNSAR_Type_NS3 r v)


def _set_CNTNSAR_Type_NS4 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTNSAR_Type_NS4 r v)


def _set_CNTNSAR_Type_NS5 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTNSAR_Type_NS5 r v)


def _set_CNTNSAR_Type_NS6 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTNSAR_Type_NS6 r v)


def _set_CNTNSAR_Type_NS7 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTNSAR_Type_NS7 r v)


def __get_ID_AA64MMFR2_EL1 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : ID_AA64MMFR2_EL1_Type := value_name
  (Mk_ID_AA64MMFR2_EL1_Type
    (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
        (Sail.BitVec.zeroExtend 0xF00000000000#48 64)))))


def __get_VTCR_EL2 (value_name : (BitVec 64)) : (BitVec 64) :=
  let tmp : VTCR_EL2_Type := value_name
  (Mk_VTCR_EL2_Type
    ((tmp &&& (Complement.complement 0xFFFFEC8001900000#64)) ||| (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.zeroExtend
        0x80000000#32 64))))


end ArmFull.Functions
