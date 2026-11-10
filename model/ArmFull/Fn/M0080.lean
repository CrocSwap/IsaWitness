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

def _get_AMEVCNTR0_EL0_Type_ACNT (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)


def _get_AMEVCNTR0_Type_ACNT (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)


def _get_AMEVCNTR1_Type_ACNT (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)


def undefined_AMEVCNTR0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_AMEVCNTR0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_AMEVCNTR1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_AMEVCNTR1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def AMEVCNTR1_read (n : Nat) : SailM (BitVec 64) := do
  let w__0 ← (( do readReg _AMEVCNTR1 ) : SailM (Vector (BitVec 64) 16) )
  let r : AMEVCNTR1_Type := (GetElem?.getElem! w__0 n)
  let w__1 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
  let r :=
    ((Sail.BitVec.updateSubrange r 63 0 (BitVec.slice (GetElem?.getElem! w__1 n) 0 64)) : (BitVec 64))
  (pure (r))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def AMEVCNTR1_set (n : Nat) (value_name : (BitVec 64)) : SailM Unit := do
  let r : AMEVCNTR1_Type := value_name
  let w__0 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
  let w__1 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
  writeReg AMEVCNTR1_EL0 (vectorUpdate w__0 n
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__1 n) 63 0 (BitVec.slice r 0 64)))
  let w__2 ← (( do readReg _AMEVCNTR1 ) : SailM (Vector (BitVec 64) 16) )
  writeReg _AMEVCNTR1 (vectorUpdate w__2 n r)


def Mk_AMCR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_AMCR_EL0_Type_CG1RZ (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _update_AMCR_EL0_Type_CG1RZ (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _update_AMCR_Type_CG1RZ (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _get_AMCR_Type_CG1RZ (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def Mk_AMCNTENSET0_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_AMCNTENCLR0_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_AMEVTYPER0_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_AMCNTENSET1_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_AMCNTENCLR1_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_AMEVCNTR0_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_AMEVCNTR0_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def AMEVCNTR0_EL0_read (n : Nat) : SailM (BitVec 64) := do
  let w__0 ← (( do readReg _AMEVCNTR0_EL0 ) : SailM (Vector (BitVec 64) 4) )
  let r : AMEVCNTR0_EL0_Type := (GetElem?.getElem! w__0 n)
  let w__1 ← (( do readReg AMEVCNTR0 ) : SailM (Vector (BitVec 64) 4) )
  let r :=
    ((Sail.BitVec.updateSubrange r 63 0 (BitVec.slice (GetElem?.getElem! w__1 n) 0 64)) : (BitVec 64))
  (pure (r))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def AMEVCNTR0_EL0_set (n : Nat) (value_name : (BitVec 64)) : SailM Unit := do
  let r : AMEVCNTR0_EL0_Type := value_name
  let w__0 ← (( do readReg AMEVCNTR0 ) : SailM (Vector (BitVec 64) 4) )
  let w__1 ← (( do readReg AMEVCNTR0 ) : SailM (Vector (BitVec 64) 4) )
  writeReg AMEVCNTR0 (vectorUpdate w__0 n
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__1 n) 63 0 (BitVec.slice r 0 64)))
  let w__2 ← (( do readReg _AMEVCNTR0_EL0 ) : SailM (Vector (BitVec 64) 4) )
  writeReg _AMEVCNTR0_EL0 (vectorUpdate w__2 n r)


def Mk_AMCFGR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_AMCFGR_EL0_Type_NCG (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _update_AMCFGR_EL0_Type_NCG (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _update_AMCFGR_Type_NCG (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _update_PMCFGR_Type_NCG (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _get_AMCFGR_Type_NCG (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _get_PMCFGR_Type_NCG (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _get_AMCFGR_EL0_Type_SIZE (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 13 8)


def _update_AMCFGR_EL0_Type_SIZE (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 8 x)


def _update_AMCFGR_Type_SIZE (v : (BitVec 32)) (x : (BitVec 6)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 8 x)


def _update_AMPIDR4_Type_SIZE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_CTIPIDR4_Type_SIZE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_EDPIDR4_Type_SIZE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_PMCFGR_Type_SIZE (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 8 x)


def _update_PMPIDR4_Type_SIZE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_AMCFGR_Type_SIZE (v : (BitVec 32)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 13 8)


def _get_AMPIDR4_Type_SIZE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_CTIPIDR4_Type_SIZE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_EDPIDR4_Type_SIZE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_PMCFGR_Type_SIZE (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 13 8)


def _get_PMPIDR4_Type_SIZE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def Mk_AMUSERENR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_AMCG1IDR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF10_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF10_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF110_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)


def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF110_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)


def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF111_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)


def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF111_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)


def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF112_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF112_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF113_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF113_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF114_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF114_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF115_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF115_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF11_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF11_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF12_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)


def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF12_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)


def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF13_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)


def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF13_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)


def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF14_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF14_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF15_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF15_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)


def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF16_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF16_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF17_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)


def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF17_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)


def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF18_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF18_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _get_AMCG1IDR_EL0_Type_AMEVCNTOFF19_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)


def _update_AMCG1IDR_EL0_Type_AMEVCNTOFF19_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)


def undefined_AMEVTYPER1_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_AMEVTYPER1_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_AMCGCR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_AMCGCR_EL0_Type_CG0NC (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _update_AMCGCR_EL0_Type_CG0NC (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_AMCGCR_Type_CG0NC (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_PMCGCR0_Type_CG0NC (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _get_AMCGCR_Type_CG0NC (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_PMCGCR0_Type_CG0NC (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_AMCGCR_EL0_Type_CG1NC (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)


def _update_AMCGCR_EL0_Type_CG1NC (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 8 x)


def _update_AMCGCR_Type_CG1NC (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 8 x)


def _update_PMCGCR0_Type_CG1NC (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 8 x)


def _get_AMCGCR_Type_CG1NC (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)


def _get_PMCGCR0_Type_CG1NC (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)


def Mk_ERRIDR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _update_ERRIDR_EL1_Type_NUM (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_ERRIDR_Type_NUM (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _get_ERRIDR_Type_NUM (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def Mk_ERRSELR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_ERXGSR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_ERXGSR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_BRBINF_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_BRBINF_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_BRBTGT_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_BRBTGT_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_BRBSRC_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_BRBSRC_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_GITS_CREADR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_GITS_CREADR_Type_Offset (v : (BitVec 64)) : (BitVec 15) :=
  (Sail.BitVec.extractLsb v 19 5)


def _update_GITS_CREADR_Type_Offset (v : (BitVec 64)) (x : (BitVec 15)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 5 x)


def _update_GITS_CWRITER_Type_Offset (v : (BitVec 64)) (x : (BitVec 15)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 5 x)


def _get_GITS_CWRITER_Type_Offset (v : (BitVec 64)) : (BitVec 15) :=
  (Sail.BitVec.extractLsb v 19 5)


def _get_GITS_CREADR_Type_Stalled (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_GITS_CREADR_Type_Stalled (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def Mk_GICR_PENDBASER_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_GICR_PENDBASER_Type_InnerCache (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 9 7)


def _update_GICR_PENDBASER_Type_InnerCache (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 7 x)


def _update_GICR_PROPBASER_Type_InnerCache (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 7 x)


def _update_GICR_VPENDBASER_Type_InnerCache (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 7 x)


def _update_GICR_VPROPBASER_Type_InnerCache (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 7 x)


def _update_GITS_CBASER_Type_InnerCache (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 59 x)


def _get_GICR_PROPBASER_Type_InnerCache (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 9 7)


def _get_GICR_VPENDBASER_Type_InnerCache (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 9 7)


def _get_GICR_VPROPBASER_Type_InnerCache (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 9 7)


def _get_GITS_CBASER_Type_InnerCache (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 61 59)


def _get_GICR_PENDBASER_Type_OuterCache (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 58 56)


def _update_GICR_PENDBASER_Type_OuterCache (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 56 x)


def _update_GICR_PROPBASER_Type_OuterCache (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 56 x)


def _update_GICR_VPENDBASER_Type_OuterCache (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 56 x)


def _update_GICR_VPROPBASER_Type_OuterCache (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 56 x)


def _update_GITS_CBASER_Type_OuterCache (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 53 x)


def _get_GICR_PROPBASER_Type_OuterCache (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 58 56)


def _get_GICR_VPENDBASER_Type_OuterCache (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 58 56)


def _get_GICR_VPROPBASER_Type_OuterCache (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 58 56)


def _get_GITS_CBASER_Type_OuterCache (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 55 53)


def _get_GICR_PENDBASER_Type_PTZ (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)


def _update_GICR_PENDBASER_Type_PTZ (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)


def _get_GICR_PENDBASER_Type_Physical_Address (v : (BitVec 64)) : (BitVec 36) :=
  (Sail.BitVec.extractLsb v 51 16)


def _update_GICR_PENDBASER_Type_Physical_Address (v : (BitVec 64)) (x : (BitVec 36)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 16 x)


def _update_GICR_PROPBASER_Type_Physical_Address (v : (BitVec 64)) (x : (BitVec 40)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 12 x)


def _update_GICR_VPENDBASER_Type_Physical_Address (v : (BitVec 64)) (x : (BitVec 36)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 16 x)


def _update_GICR_VPROPBASER_Type_Physical_Address (v : (BitVec 64)) (x : (BitVec 40)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 12 x)


def _update_GITS_CBASER_Type_Physical_Address (v : (BitVec 64)) (x : (BitVec 40)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 12 x)


def _get_GICR_PROPBASER_Type_Physical_Address (v : (BitVec 64)) : (BitVec 40) :=
  (Sail.BitVec.extractLsb v 51 12)


def _get_GICR_VPENDBASER_Type_Physical_Address (v : (BitVec 64)) : (BitVec 36) :=
  (Sail.BitVec.extractLsb v 51 16)


def _get_GICR_VPROPBASER_Type_Physical_Address (v : (BitVec 64)) : (BitVec 40) :=
  (Sail.BitVec.extractLsb v 51 12)


def _get_GITS_CBASER_Type_Physical_Address (v : (BitVec 64)) : (BitVec 40) :=
  (Sail.BitVec.extractLsb v 51 12)


def _get_GICR_PENDBASER_Type_Shareability (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)


def _update_GICR_PENDBASER_Type_Shareability (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)


def _update_GICR_PROPBASER_Type_Shareability (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)


def _update_GICR_VPENDBASER_Type_Shareability (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)


def _update_GICR_VPROPBASER_Type_Shareability (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)


def _update_GITS_CBASER_Type_Shareability (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)


def _get_GICR_PROPBASER_Type_Shareability (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)


def _get_GICR_VPENDBASER_Type_Shareability (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)


def _get_GICR_VPROPBASER_Type_Shareability (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)


def _get_GITS_CBASER_Type_Shareability (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)


def Mk_GICR_PROPBASER_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_GICR_VPROPBASER_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_GICR_VPROPBASER_Type_Entry_Size (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 61 59)


def _update_GICR_VPROPBASER_Type_Entry_Size (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 59 x)


def _get_GICR_VPROPBASER_Type_Indirect (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 55 55)


def _update_GICR_VPROPBASER_Type_Indirect (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)


def _get_GICR_VPROPBASER_Type_Page_Size (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 54 53)


def _update_GICR_VPROPBASER_Type_Page_Size (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 53 x)


def _get_GICR_VPROPBASER_Type_Size (v : (BitVec 64)) : (BitVec 7) :=
  (Sail.BitVec.extractLsb v 6 0)


def _update_GICR_VPROPBASER_Type_Size (v : (BitVec 64)) (x : (BitVec 7)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 0 x)


def _update_GITS_CBASER_Type_Size (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _get_GITS_CBASER_Type_Size (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def Mk_EDPFR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_GICR_CLRLPIR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_GICR_INVALLR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_GICR_INVALLR_Type_vPEID (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 47 32)


def _update_GICR_INVALLR_Type_vPEID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 32 x)


def _update_GICR_INVLPIR_Type_vPEID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 32 x)


def _update_GICR_VPENDBASER_Type_vPEID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_GICR_VSGIR_Type_vPEID (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_GITS_SGIR_Type_vPEID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 32 x)


def _get_GICR_INVLPIR_Type_vPEID (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 47 32)


def _get_GICR_VPENDBASER_Type_vPEID (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _get_GICR_VSGIR_Type_vPEID (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _get_GITS_SGIR_Type_vPEID (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 47 32)


def Mk_EDHSR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_EDHSR_Type_FnP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _update_EDHSR_Type_FnP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _get_EDHSR_Type_VNCR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _update_EDHSR_Type_VNCR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _get_EDHSR_Type_WPF (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _update_EDHSR_Type_WPF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _get_EDHSR_Type_WPT (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 23 18)


def _update_EDHSR_Type_WPT (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 18 x)


def _get_EDHSR_Type_WPTV (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _update_EDHSR_Type_WPTV (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


end ArmFull.Functions
