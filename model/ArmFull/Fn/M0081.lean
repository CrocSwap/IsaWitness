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

def Mk_EDPCSR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_GICR_VPENDBASER_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_GICR_VPENDBASER_Type_Dirty (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)


def _update_GICR_VPENDBASER_Type_Dirty (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)


def _get_GICR_VPENDBASER_Type_Doorbell (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)


def _update_GICR_VPENDBASER_Type_Doorbell (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)


def _get_GICR_VPENDBASER_Type_IDAI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)


def _update_GICR_VPENDBASER_Type_IDAI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)


def _get_GICR_VPENDBASER_Type_PendingLast (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)


def _update_GICR_VPENDBASER_Type_PendingLast (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)


def _get_GICR_VPENDBASER_Type_VGrp0En (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)


def _update_GICR_VPENDBASER_Type_VGrp0En (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)


def _get_GICR_VPENDBASER_Type_VGrp1En (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)


def _update_GICR_VPENDBASER_Type_VGrp1En (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)


def Mk_GITS_TYPER_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_GITS_TYPER_Type_CCT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_GITS_TYPER_Type_CCT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_GITS_TYPER_Type_CIDbits (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)


def _update_GITS_TYPER_Type_CIDbits (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)


def _get_GITS_TYPER_Type_CIL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 36 36)


def _update_GITS_TYPER_Type_CIL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)


def _get_GITS_TYPER_Type_Devbits (v : (BitVec 64)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 17 13)


def _update_GITS_TYPER_Type_Devbits (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 13 x)


def _get_GITS_TYPER_Type_HCC (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)


def _update_GITS_TYPER_Type_HCC (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 24 x)


def _get_GITS_TYPER_Type_ID_bits (v : (BitVec 64)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 12 8)


def _update_GITS_TYPER_Type_ID_bits (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 8 x)


def _get_GITS_TYPER_Type_INV (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 46 46)


def _update_GITS_TYPER_Type_INV (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 46 x)


def _get_GITS_TYPER_Type_ITT_entry_size (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_GITS_TYPER_Type_ITT_entry_size (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_GITS_TYPER_Type_PTA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)


def _update_GITS_TYPER_Type_PTA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)


def _get_GITS_TYPER_Type_Physical (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_GITS_TYPER_Type_Physical (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_GITS_TYPER_Type_SVPET (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 42 41)


def _update_GITS_TYPER_Type_SVPET (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 41 x)


def _get_GITS_TYPER_Type_UMSI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 44 44)


def _update_GITS_TYPER_Type_UMSI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)


def _update_GITS_STATUSR_Type_UMSI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_GITS_STATUSR_Type_UMSI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _get_GITS_TYPER_Type_UMSIirq (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 45 45)


def _update_GITS_TYPER_Type_UMSIirq (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 45 x)


def _update_GITS_CTLR_Type_UMSIirq (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)


def _get_GITS_CTLR_Type_UMSIirq (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)


def _get_GITS_TYPER_Type_VMAPP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)


def _update_GITS_TYPER_Type_VMAPP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)


def _get_GITS_TYPER_Type_VMOVP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)


def _update_GITS_TYPER_Type_VMOVP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)


def _get_GITS_TYPER_Type_VSGI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 39 39)


def _update_GITS_TYPER_Type_VSGI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 39 x)


def _get_GITS_TYPER_Type_Virtual (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_GITS_TYPER_Type_Virtual (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_GITS_TYPER_Type_nID (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 43 43)


def _update_GITS_TYPER_Type_nID (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)


def Mk_GITS_SGIR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_EDDFR1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_GITS_CWRITER_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_GITS_CWRITER_Type_Retry (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_GITS_CWRITER_Type_Retry (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def Mk_EDDFR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_GICR_INVLPIR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_EDAA32PFR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_EDAA32PFR_Type_MSA_frac (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_EDAA32PFR_Type_MSA_frac (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def Mk_GITS_CBASER_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_GICR_SETLPIR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_PMCFGR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_PMCFGR_Type_CCD (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _update_PMCFGR_Type_CCD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _get_PMCFGR_Type_NA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _update_PMCFGR_Type_NA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def Mk_PMIIDR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_PMIIDR_Type_ProductID (v : (BitVec 64)) : (BitVec 12) :=
  (Sail.BitVec.extractLsb v 31 20)


def _update_PMIIDR_Type_ProductID (v : (BitVec 64)) (x : (BitVec 12)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 20 x)


def _update_AMIIDR_Type_ProductID (v : (BitVec 32)) (x : (BitVec 12)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 20 x)


def _update_GICD_IIDR_Type_ProductID (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)


def _update_GICM_IIDR_Type_ProductID (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)


def _update_GICR_IIDR_Type_ProductID (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)


def _update_GITS_IIDR_Type_ProductID (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)


def _get_AMIIDR_Type_ProductID (v : (BitVec 32)) : (BitVec 12) :=
  (Sail.BitVec.extractLsb v 31 20)


def _get_GICD_IIDR_Type_ProductID (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)


def _get_GICM_IIDR_Type_ProductID (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)


def _get_GICR_IIDR_Type_ProductID (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)


def _get_GITS_IIDR_Type_ProductID (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)


def Mk_PMPCSCTL_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_PMVCIDSR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def AIFSR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AIFSR_NS ) : SailM AIFSR_Type )
  let w__0 ← (( do readReg AFSR1_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def AIFSR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AIFSR_Type := value_name
  let w__0 ← (( do readReg AFSR1_EL1 ) : SailM (BitVec 64) )
  writeReg AFSR1_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _AIFSR_NS r


def Mk_ID_DFR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def HACR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HACR ) : SailM HACR_Type )
  let w__0 ← (( do readReg HACR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def HACR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HACR_Type := value_name
  let w__0 ← (( do readReg HACR_EL2 ) : SailM (BitVec 64) )
  writeReg HACR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _HACR r


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def DBGBVR_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGBVR_Type := value_name
  let w__0 ← (( do readReg DBGBVR_EL1 ) : SailM (Vector (BitVec 64) 64) )
  let w__1 ← (( do readReg DBGBVR_EL1 ) : SailM (Vector (BitVec 64) 64) )
  writeReg DBGBVR_EL1 (vectorUpdate w__0 n
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__1 n) 31 0 (BitVec.slice r 0 32)))
  let w__2 ← (( do readReg _DBGBVR ) : SailM (Vector (BitVec 32) 16) )
  writeReg _DBGBVR (vectorUpdate w__2 n r)


def PMCEID1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _PMCEID1 ) : SailM PMCEID1_Type )
  let w__0 ← (( do readReg PMCEID1_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def PMCNTENSET_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMCNTENSET_Type := value_name
  let w__0 ← (( do readReg PMCNTENSET_EL0 ) : SailM (BitVec 64) )
  writeReg PMCNTENSET_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _PMCNTENSET r


def Mk_ID_MMFR3_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def PMCEID0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _PMCEID0 ) : SailM PMCEID0_Type )
  let w__0 ← (( do readReg PMCEID0_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def DBGBXVR_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGBXVR_Type := value_name
  let w__0 ← (( do readReg DBGBVR_EL1 ) : SailM (Vector (BitVec 64) 64) )
  let w__1 ← (( do readReg DBGBVR_EL1 ) : SailM (Vector (BitVec 64) 64) )
  writeReg DBGBVR_EL1 (vectorUpdate w__0 n
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__1 n) 63 32 (BitVec.slice r 0 32)))
  let w__2 ← (( do readReg _DBGBXVR ) : SailM (Vector (BitVec 32) 16) )
  writeReg _DBGBXVR (vectorUpdate w__2 n r)


def HACTLR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HACTLR ) : SailM HACTLR_Type )
  let w__0 ← (( do readReg ACTLR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def HACTLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HACTLR_Type := value_name
  let w__0 ← (( do readReg ACTLR_EL2 ) : SailM (BitVec 64) )
  writeReg ACTLR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _HACTLR r


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def DBGWVR_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGWVR_Type := value_name
  let w__0 ← (( do readReg DBGWVR_EL1 ) : SailM (Vector (BitVec 64) 64) )
  let w__1 ← (( do readReg DBGWVR_EL1 ) : SailM (Vector (BitVec 64) 64) )
  writeReg DBGWVR_EL1 (vectorUpdate w__0 n
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__1 n) 31 0 (BitVec.slice r 0 32)))
  let w__2 ← (( do readReg _DBGWVR ) : SailM (Vector (BitVec 32) 16) )
  writeReg _DBGWVR (vectorUpdate w__2 n r)


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICV_AP0R_read (n : Nat) : SailM (BitVec 32) := do
  let w__0 ← (( do readReg _ICV_AP0R ) : SailM (Vector (BitVec 32) 4) )
  let r : ICV_AP0R_Type := (GetElem?.getElem! w__0 n)
  let w__1 ← (( do readReg ICV_AP0R_EL1 ) : SailM (Vector (BitVec 64) 4) )
  let r :=
    ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! w__1 n) 0 32)) : (BitVec 32))
  (pure (r))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICV_AP0R_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_AP0R_Type := value_name
  let w__0 ← (( do readReg ICV_AP0R_EL1 ) : SailM (Vector (BitVec 64) 4) )
  let w__1 ← (( do readReg ICV_AP0R_EL1 ) : SailM (Vector (BitVec 64) 4) )
  writeReg ICV_AP0R_EL1 (vectorUpdate w__0 n
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__1 n) 31 0 (BitVec.slice r 0 32)))
  let w__2 ← (( do readReg _ICV_AP0R ) : SailM (Vector (BitVec 32) 4) )
  writeReg _ICV_AP0R (vectorUpdate w__2 n r)


def HMAIR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HMAIR0_Type := value_name
  let w__0 ← (( do readReg MAIR_EL2 ) : SailM (BitVec 64) )
  writeReg MAIR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _HMAIR0 r


def DACR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DACR_Type := value_name
  let w__0 ← (( do readReg DACR32_EL2 ) : SailM (BitVec 64) )
  writeReg DACR32_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _DACR_NS r


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def DBGWCR_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGWCR_Type := value_name
  let w__0 ← (( do readReg DBGWCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
  let w__1 ← (( do readReg DBGWCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
  writeReg DBGWCR_EL1 (vectorUpdate w__0 n
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__1 n) 31 0 (BitVec.slice r 0 32)))
  let w__2 ← (( do readReg _DBGWCR ) : SailM (Vector (BitVec 32) 16) )
  writeReg _DBGWCR (vectorUpdate w__2 n r)


def Mk_DBGDEVID1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_DBGDEVID1_Type_PCSROffset (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_DBGDEVID1_Type_PCSROffset (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_EDDEVID1_Type_PCSROffset (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_EDDEVID1_Type_PCSROffset (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def PMINTENCLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMINTENCLR_Type := value_name
  let w__0 ← (( do readReg PMINTENCLR_EL1 ) : SailM (BitVec 64) )
  writeReg PMINTENCLR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _PMINTENCLR r


def Mk_ID_MMFR4_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def TPIDRURW_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _TPIDRURW_NS ) : SailM TPIDRURW_Type )
  let w__0 ← (( do readReg TPIDR_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def TPIDRURW_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TPIDRURW_Type := value_name
  let w__0 ← (( do readReg TPIDR_EL0 ) : SailM (BitVec 64) )
  writeReg TPIDR_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _TPIDRURW_NS r


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICV_AP1R_read (n : Nat) : SailM (BitVec 32) := do
  let w__0 ← (( do readReg _ICV_AP1R ) : SailM (Vector (BitVec 32) 4) )
  let r : ICV_AP1R_Type := (GetElem?.getElem! w__0 n)
  let w__1 ← (( do readReg ICV_AP1R_EL1 ) : SailM (Vector (BitVec 64) 4) )
  let r :=
    ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! w__1 n) 0 32)) : (BitVec 32))
  (pure (r))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICV_AP1R_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_AP1R_Type := value_name
  let w__0 ← (( do readReg ICV_AP1R_EL1 ) : SailM (Vector (BitVec 64) 4) )
  let w__1 ← (( do readReg ICV_AP1R_EL1 ) : SailM (Vector (BitVec 64) 4) )
  writeReg ICV_AP1R_EL1 (vectorUpdate w__0 n
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__1 n) 31 0 (BitVec.slice r 0 32)))
  let w__2 ← (( do readReg _ICV_AP1R ) : SailM (Vector (BitVec 32) 4) )
  writeReg _ICV_AP1R (vectorUpdate w__2 n r)


def ADFSR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ADFSR_NS ) : SailM ADFSR_Type )
  let w__0 ← (( do readReg AFSR0_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ADFSR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ADFSR_Type := value_name
  let w__0 ← (( do readReg AFSR0_EL1 ) : SailM (BitVec 64) )
  writeReg AFSR0_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ADFSR_NS r


def _get_CNTHCTL_Type_PL1PCEN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_CNTHCTL_Type_PL1PCEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_CNTHCTL_Type_PL1PCTEN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_CNTHCTL_Type_PL1PCTEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def REVIDR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _REVIDR ) : SailM REVIDR_Type )
  let w__0 ← (( do readReg REVIDR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def Mk_ID_MMFR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICC_MSRE_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PMMIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def MAIR0_S_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : MAIR0_Type := value_name
  let w__0 ← (( do readReg PRRR_S ) : SailM (BitVec 32) )
  writeReg PRRR_S (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _MAIR0_S r


def Mk_FPSID_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_FPSID_Type_Subarchitecture (v : (BitVec 32)) : (BitVec 7) :=
  (Sail.BitVec.extractLsb v 22 16)


def _update_FPSID_Type_Subarchitecture (v : (BitVec 32)) (x : (BitVec 7)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 16 x)


def Mk_ICC_MCTLR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def TPIDRURO_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _TPIDRURO_NS ) : SailM TPIDRURO_Type )
  let w__0 ← (( do readReg TPIDRRO_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def TPIDRURO_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TPIDRURO_Type := value_name
  let w__0 ← (( do readReg TPIDRRO_EL0 ) : SailM (BitVec 64) )
  writeReg TPIDRRO_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _TPIDRURO_NS r


def undefined_DBGDTRTXext_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_DBGDTRTXext_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_DBGDTRTXext_Type_DTRTX (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def _update_DBGDTRTXext_Type_DTRTX (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def _update_DBGDTRTXint_Type_DTRTX (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def _get_DBGDTRTXint_Type_DTRTX (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def DBGDTRTXext_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DBGDTRTXext ) : SailM DBGDTRTXext_Type )
  let w__0 ← (( do readReg OSDTRTX_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def DBGDTRTXext_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGDTRTXext_Type := value_name
  let w__0 ← (( do readReg OSDTRTX_EL1 ) : SailM (BitVec 64) )
  writeReg OSDTRTX_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _DBGDTRTXext r


def ACTLR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ACTLR_NS ) : SailM ACTLR_Type )
  let w__0 ← (( do readReg ACTLR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ACTLR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ACTLR_Type := value_name
  let w__0 ← (( do readReg ACTLR_EL1 ) : SailM (BitVec 64) )
  writeReg ACTLR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ACTLR_NS r


def Mk_MVFR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def undefined_DBGOSLAR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_DBGOSLAR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_DBGOSLAR_Type_OSLA (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def _update_DBGOSLAR_Type_OSLA (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def undefined_DBGDTRRXext_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_DBGDTRRXext_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_DBGDTRRXext_Type_DTRRX (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def _update_DBGDTRRXext_Type_DTRRX (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def _update_DBGDTRRXint_Type_DTRRX (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def _get_DBGDTRRXint_Type_DTRRX (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def DBGDTRRXext_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DBGDTRRXext ) : SailM DBGDTRRXext_Type )
  let w__0 ← (( do readReg OSDTRRX_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def DBGDTRRXext_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGDTRRXext_Type := value_name
  let w__0 ← (( do readReg OSDTRRX_EL1 ) : SailM (BitVec 64) )
  writeReg OSDTRRX_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _DBGDTRRXext r


end ArmFull.Functions
