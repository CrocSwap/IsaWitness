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

def _update_HFGWTR_EL2_Type_TTBR1_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)


def _update_HFGRTR_EL2_Type_TTBR1_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)


def _get_HFGRTR_EL2_Type_TTBR1_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)


def _get_HFGWTR_EL2_Type_VBAR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 38 38)


def _update_HFGWTR_EL2_Type_VBAR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)


def _update_HFGRTR_EL2_Type_VBAR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)


def _get_HFGRTR_EL2_Type_VBAR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 38 38)


def _get_HFGWTR_EL2_Type_nACCDATA_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 50 50)


def _update_HFGWTR_EL2_Type_nACCDATA_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 50 50 x)


def _update_HFGRTR_EL2_Type_nACCDATA_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 50 50 x)


def _get_HFGRTR_EL2_Type_nACCDATA_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 50 50)


def _get_HFGWTR_EL2_Type_nAMAIR2_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)


def _update_HFGWTR_EL2_Type_nAMAIR2_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)


def _update_HFGRTR_EL2_Type_nAMAIR2_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)


def _get_HFGRTR_EL2_Type_nAMAIR2_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)


def _get_HFGWTR_EL2_Type_nGCS_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 52 52)


def _update_HFGWTR_EL2_Type_nGCS_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)


def _update_HFGRTR_EL2_Type_nGCS_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)


def _get_HFGRTR_EL2_Type_nGCS_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 52 52)


def _get_HFGWTR_EL2_Type_nGCS_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 53 53)


def _update_HFGWTR_EL2_Type_nGCS_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 53 x)


def _update_HFGRTR_EL2_Type_nGCS_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 53 x)


def _get_HFGRTR_EL2_Type_nGCS_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 53 53)


def _get_HFGWTR_EL2_Type_nMAIR2_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)


def _update_HFGWTR_EL2_Type_nMAIR2_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)


def _update_HFGRTR_EL2_Type_nMAIR2_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)


def _get_HFGRTR_EL2_Type_nMAIR2_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)


def _get_HFGWTR_EL2_Type_nPIRE0_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 57 57)


def _update_HFGWTR_EL2_Type_nPIRE0_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)


def _update_HFGRTR_EL2_Type_nPIRE0_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)


def _get_HFGRTR_EL2_Type_nPIRE0_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 57 57)


def _get_HFGWTR_EL2_Type_nPIR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)


def _update_HFGWTR_EL2_Type_nPIR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)


def _update_HFGRTR_EL2_Type_nPIR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)


def _get_HFGRTR_EL2_Type_nPIR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)


def _get_HFGWTR_EL2_Type_nPOR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)


def _update_HFGWTR_EL2_Type_nPOR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)


def _update_HFGRTR_EL2_Type_nPOR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)


def _get_HFGRTR_EL2_Type_nPOR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)


def _get_HFGWTR_EL2_Type_nPOR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)


def _update_HFGWTR_EL2_Type_nPOR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)


def _update_HFGRTR_EL2_Type_nPOR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)


def _get_HFGRTR_EL2_Type_nPOR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)


def _get_HFGWTR_EL2_Type_nRCWMASK_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 56 56)


def _update_HFGWTR_EL2_Type_nRCWMASK_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 56 x)


def _update_HFGRTR_EL2_Type_nRCWMASK_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 56 x)


def _get_HFGRTR_EL2_Type_nRCWMASK_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 56 56)


def _get_HFGWTR_EL2_Type_nS2POR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)


def _update_HFGWTR_EL2_Type_nS2POR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)


def _update_HFGRTR_EL2_Type_nS2POR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)


def _get_HFGRTR_EL2_Type_nS2POR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)


def _get_HFGWTR_EL2_Type_nSMPRI_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 54 54)


def _update_HFGWTR_EL2_Type_nSMPRI_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)


def _update_HFGRTR_EL2_Type_nSMPRI_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)


def _get_HFGRTR_EL2_Type_nSMPRI_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 54 54)


def _get_HFGWTR_EL2_Type_nTPIDR2_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 55 55)


def _update_HFGWTR_EL2_Type_nTPIDR2_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)


def _update_HFGRTR_EL2_Type_nTPIDR2_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)


def _get_HFGRTR_EL2_Type_nTPIDR2_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 55 55)


def Mk_SMPRI_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_PMUSERENR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_PMUSERENR_EL0_Type_CR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_PMUSERENR_EL0_Type_CR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_PMUSERENR_Type_CR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_PMUSERENR_Type_CR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_PMUSERENR_EL0_Type_ER (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_PMUSERENR_EL0_Type_ER (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_PMUSERENR_Type_ER (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_PMUSERENR_Type_ER (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_PMUSERENR_EL0_Type_IR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _update_PMUSERENR_EL0_Type_IR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_GICR_CTLR_Type_IR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_GICR_CTLR_Type_IR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_PMUSERENR_EL0_Type_TID (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _update_PMUSERENR_EL0_Type_TID (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_PMUSERENR_Type_TID (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _get_PMUSERENR_Type_TID (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_PMUSERENR_EL0_Type_UEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _update_PMUSERENR_EL0_Type_UEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _update_PMCFGR_Type_UEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)


def _get_PMCFGR_Type_UEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)


def Mk_ICV_CTLR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_ICV_IAR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def __set_GPCCR_EL3 (value_name : (BitVec 64)) : SailM Unit := do
  let r : GPCCR_EL3_Type := value_name
  let w__0 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
  writeReg GPCCR_EL3 (Sail.BitVec.updateSubrange w__0 19 0 (BitVec.slice r 0 20))
  let w__1 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
  writeReg GPCCR_EL3 (Sail.BitVec.updateSubrange w__1 63 24 (BitVec.slice r 24 40))


def Mk_ID_PFR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ID_PFR0_EL1_Type_State0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_ID_PFR0_EL1_Type_State0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_ID_PFR0_Type_State0 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_ID_PFR0_EL1_Type_State1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_ID_PFR0_EL1_Type_State1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_ID_PFR0_Type_State1 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_ID_PFR0_EL1_Type_State2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _update_ID_PFR0_EL1_Type_State2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_ID_PFR0_Type_State2 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _get_ID_PFR0_EL1_Type_State3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _update_ID_PFR0_EL1_Type_State3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _get_ID_PFR0_Type_State3 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def Mk_MVFR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_MVFR1_EL1_Type_FPDNaN (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_MVFR1_EL1_Type_FPDNaN (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_MVFR1_Type_FPDNaN (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_MVFR1_EL1_Type_FPFtZ (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_MVFR1_EL1_Type_FPFtZ (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_MVFR1_Type_FPFtZ (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_MVFR1_EL1_Type_FPHP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _update_MVFR1_EL1_Type_FPHP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _get_MVFR1_Type_FPHP (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_MVFR1_EL1_Type_SIMDFMAC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _update_MVFR1_EL1_Type_SIMDFMAC (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _get_MVFR1_Type_SIMDFMAC (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _get_MVFR1_EL1_Type_SIMDHP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _update_MVFR1_EL1_Type_SIMDHP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _get_MVFR1_Type_SIMDHP (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _get_MVFR1_EL1_Type_SIMDInt (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _update_MVFR1_EL1_Type_SIMDInt (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _get_MVFR1_Type_SIMDInt (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _get_MVFR1_EL1_Type_SIMDLS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _update_MVFR1_EL1_Type_SIMDLS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_MVFR1_Type_SIMDLS (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _get_MVFR1_EL1_Type_SIMDSP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_MVFR1_EL1_Type_SIMDSP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_MVFR1_Type_SIMDSP (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def Mk_HDFGWTR2_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_HDFGWTR2_EL2_Type_nMDSELR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _update_HDFGWTR2_EL2_Type_nMDSELR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_HDFGRTR2_EL2_Type_nMDSELR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _get_HDFGRTR2_EL2_Type_nMDSELR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_HDFGWTR2_EL2_Type_nPMECR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_HDFGWTR2_EL2_Type_nPMECR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_HDFGRTR2_EL2_Type_nPMECR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_HDFGRTR2_EL2_Type_nPMECR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_HDFGWTR2_EL2_Type_nPMIAR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_HDFGWTR2_EL2_Type_nPMIAR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_HDFGRTR2_EL2_Type_nPMIAR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_HDFGRTR2_EL2_Type_nPMIAR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_HDFGWTR2_EL2_Type_nPMICFILTR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_HDFGWTR2_EL2_Type_nPMICFILTR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_HDFGRTR2_EL2_Type_nPMICFILTR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_HDFGRTR2_EL2_Type_nPMICFILTR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_HDFGWTR2_EL2_Type_nPMICNTR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_HDFGWTR2_EL2_Type_nPMICNTR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_HDFGRTR2_EL2_Type_nPMICNTR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_HDFGRTR2_EL2_Type_nPMICNTR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_HDFGWTR2_EL2_Type_nPMSDSFR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)


def _update_HDFGWTR2_EL2_Type_nPMSDSFR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)


def _update_HDFGRTR2_EL2_Type_nPMSDSFR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)


def _get_HDFGRTR2_EL2_Type_nPMSDSFR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)


def _get_HDFGWTR2_EL2_Type_nPMSSCR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _update_HDFGWTR2_EL2_Type_nPMSSCR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _update_HDFGRTR2_EL2_Type_nPMSSCR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _get_HDFGRTR2_EL2_Type_nPMSSCR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _get_HDFGWTR2_EL2_Type_nPMUACR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _update_HDFGWTR2_EL2_Type_nPMUACR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _update_HDFGRTR2_EL2_Type_nPMUACR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_HDFGRTR2_EL2_Type_nPMUACR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _get_HDFGWTR2_EL2_Type_nPMZR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


def _update_HDFGWTR2_EL2_Type_nPMZR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)


def _get_HDFGWTR2_EL2_Type_nSPMACCESSR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _update_HDFGWTR2_EL2_Type_nSPMACCESSR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _update_HDFGRTR2_EL2_Type_nSPMACCESSR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _get_HDFGRTR2_EL2_Type_nSPMACCESSR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _get_HDFGWTR2_EL2_Type_nSPMCNTEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)


def _update_HDFGWTR2_EL2_Type_nSPMCNTEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _update_HDFGRTR2_EL2_Type_nSPMCNTEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _get_HDFGRTR2_EL2_Type_nSPMCNTEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)


def _get_HDFGWTR2_EL2_Type_nSPMCR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _update_HDFGWTR2_EL2_Type_nSPMCR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _update_HDFGRTR2_EL2_Type_nSPMCR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _get_HDFGRTR2_EL2_Type_nSPMCR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _get_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)


def _update_HDFGWTR2_EL2_Type_nSPMEVCNTRn_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)


def _update_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)


def _get_HDFGRTR2_EL2_Type_nSPMEVCNTRn_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)


def _get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def _update_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


def _update_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


def _get_HDFGRTR2_EL2_Type_nSPMEVTYPERn_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def _get_HDFGWTR2_EL2_Type_nSPMINTEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _update_HDFGWTR2_EL2_Type_nSPMINTEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _update_HDFGRTR2_EL2_Type_nSPMINTEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _get_HDFGRTR2_EL2_Type_nSPMINTEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _get_HDFGWTR2_EL2_Type_nSPMOVS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _update_HDFGWTR2_EL2_Type_nSPMOVS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _update_HDFGRTR2_EL2_Type_nSPMOVS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _get_HDFGRTR2_EL2_Type_nSPMOVS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _get_HDFGWTR2_EL2_Type_nSPMSCR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _update_HDFGWTR2_EL2_Type_nSPMSCR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _update_HDFGRTR2_EL2_Type_nSPMSCR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _get_HDFGRTR2_EL2_Type_nSPMSCR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _get_HDFGWTR2_EL2_Type_nSPMSELR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _update_HDFGWTR2_EL2_Type_nSPMSELR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _update_HDFGRTR2_EL2_Type_nSPMSELR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _get_HDFGRTR2_EL2_Type_nSPMSELR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def Mk_ID_ISAR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ID_ISAR0_EL1_Type_BitCount (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_ID_ISAR0_EL1_Type_BitCount (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_ID_ISAR0_Type_BitCount (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_ID_ISAR0_EL1_Type_BitField (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _update_ID_ISAR0_EL1_Type_BitField (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


end ArmFull.Functions
