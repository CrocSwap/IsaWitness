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

def _update_TTBR0_Type_S (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_TTBR1_Type_S (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_VTCR_Type_S (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_DBGVCR32_EL2_Type_S (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_DBGVCR_Type_S (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_PAR_EL1_Type_S (v : (BitVec 128)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def _get_TTBR0_Type_S (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_TTBR1_Type_S (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_VTCR_Type_S (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def Hint_Branch (hint : BranchType) : SailM Unit := do
  writeReg Branchtypetaken hint


/-- Type quantifiers: x : Int -/
def FloorPow2 (x : Int) : SailM Nat := do
  ArmFull.assert (x ≥b 0) "sail-arm/v8_base.sail:6832.17-6832.18"
  let n : Int := 1
  if ((x == 0) : Bool)
  then (pure (0))
  else
    (do
      let n ← (( do
        let loop_vars ← sailWhileFuelM (α := Int) (fuel := 1048576) (fun n => (pure (x ≥b (2 ^i n)))) n
          fun n => do (pure ((n +i 1) : Int))
        (pure loop_vars) ) : SailM Int )
      let n : Int := n
      let r : Nat := (Sail.Int.toNatChecked ((2 ^i (n -i 1))))
      ArmFull.assert (r ≥b 0) "sail-arm/v8_base.sail:6842.17-6842.18"
      (pure (r)))


def undefined_ZCR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_ZCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ZCR_EL1_Type_LEN (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_ZCR_EL1_Type_LEN (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_SMCR_EL1_Type_LEN (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_SMCR_EL2_Type_LEN (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_SMCR_EL3_Type_LEN (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_ZCR_EL2_Type_LEN (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_ZCR_EL3_Type_LEN (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_SMCR_EL1_Type_LEN (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_SMCR_EL2_Type_LEN (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_SMCR_EL3_Type_LEN (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_ZCR_EL2_Type_LEN (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_ZCR_EL3_Type_LEN (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def undefined_ZCR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_ZCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_ZCR_EL3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_ZCR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def MaxImplementedSVL (_ : Unit) : SailM Int := do
  readReg __max_implemented_smeveclen


/-- Type quantifiers: nbits : Int -/
def SupportedPowerTwoSVL (nbits : Int) : Bool :=
  true


def undefined_SMCR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_SMCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_SMCR_EL1_Type_EZT0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _update_SMCR_EL1_Type_EZT0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_SMCR_EL2_Type_EZT0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_SMCR_EL3_Type_EZT0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _get_SMCR_EL2_Type_EZT0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_SMCR_EL3_Type_EZT0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_SMCR_EL1_Type_FA64 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _update_SMCR_EL1_Type_FA64 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_ID_AA64SMFR0_EL1_Type_FA64 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)


def _update_SMCR_EL2_Type_FA64 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_SMCR_EL3_Type_FA64 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _get_ID_AA64SMFR0_EL1_Type_FA64 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)


def _get_SMCR_EL2_Type_FA64 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_SMCR_EL3_Type_FA64 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def undefined_SMCR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_SMCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_SMCR_EL3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_SMCR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_GCSPR_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_GCSPR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_GCSPR_EL0_Type_PTR (v : (BitVec 64)) : (BitVec 61) :=
  (Sail.BitVec.extractLsb v 63 3)


def _update_GCSPR_EL0_Type_PTR (v : (BitVec 64)) (x : (BitVec 61)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 3 x)


def _update_GCSPR_EL1_Type_PTR (v : (BitVec 64)) (x : (BitVec 61)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 3 x)


def _update_GCSPR_EL2_Type_PTR (v : (BitVec 64)) (x : (BitVec 61)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 3 x)


def _update_GCSPR_EL3_Type_PTR (v : (BitVec 64)) (x : (BitVec 61)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 3 x)


def _update_PMBPTR_EL1_Type_PTR (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)


def _get_GCSPR_EL1_Type_PTR (v : (BitVec 64)) : (BitVec 61) :=
  (Sail.BitVec.extractLsb v 63 3)


def _get_GCSPR_EL2_Type_PTR (v : (BitVec 64)) : (BitVec 61) :=
  (Sail.BitVec.extractLsb v 63 3)


def _get_GCSPR_EL3_Type_PTR (v : (BitVec 64)) : (BitVec 61) :=
  (Sail.BitVec.extractLsb v 63 3)


def _get_PMBPTR_EL1_Type_PTR (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)


def undefined_GCSPR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_GCSPR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_GCSPR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_GCSPR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_GCSPR_EL3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_GCSPR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_CPACR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CPACR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_CPACR_EL1_Type_E0POE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _update_CPACR_EL1_Type_E0POE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _update_CPTR_EL2_Type_E0POE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _update_TCR2_EL1_Type_E0POE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_TCR2_EL2_Type_E0POE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_CPTR_EL2_Type_E0POE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _get_TCR2_EL1_Type_E0POE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_TCR2_EL2_Type_E0POE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_CPACR_EL1_Type_FPEN (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 21 20)


def _update_CPACR_EL1_Type_FPEN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 20 x)


def _update_CPTR_EL2_Type_FPEN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 20 x)


def _get_CPTR_EL2_Type_FPEN (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 21 20)


def _get_CPACR_EL1_Type_SMEN (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)


def _update_CPACR_EL1_Type_SMEN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 24 x)


def _update_CPTR_EL2_Type_SMEN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 24 x)


def _get_CPTR_EL2_Type_SMEN (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)


def _get_CPACR_EL1_Type_TTA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _update_CPACR_EL1_Type_TTA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_CPTR_EL3_Type_TTA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def _update_HCPTR_Type_TTA (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def _get_CPTR_EL3_Type_TTA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def _get_HCPTR_Type_TTA (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def _get_CPACR_EL1_Type_ZEN (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 17 16)


def _update_CPACR_EL1_Type_ZEN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 16 x)


def _update_CPTR_EL2_Type_ZEN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 16 x)


def _get_CPTR_EL2_Type_ZEN (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 17 16)


def undefined_CPTR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CPTR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_CPTR_EL2_Type_TAM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _update_CPTR_EL2_Type_TAM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_CPTR_EL3_Type_TAM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_HCPTR_Type_TAM (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _get_CPTR_EL3_Type_TAM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_HCPTR_Type_TAM (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_CPTR_EL2_Type_TCPAC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _update_CPTR_EL2_Type_TCPAC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_CPTR_EL3_Type_TCPAC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_HCPTR_Type_TCPAC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _get_CPTR_EL3_Type_TCPAC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_HCPTR_Type_TCPAC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_CPTR_EL2_Type_TFP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _update_CPTR_EL2_Type_TFP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _update_CPTR_EL3_Type_TFP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _get_CPTR_EL3_Type_TFP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _get_CPTR_EL2_Type_TSM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _update_CPTR_EL2_Type_TSM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _get_CPTR_EL2_Type_TZ (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)


def _update_CPTR_EL2_Type_TZ (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)


def undefined_CPTR_EL3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CPTR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_CPTR_EL3_Type_ESM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _update_CPTR_EL3_Type_ESM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _get_CPTR_EL3_Type_EZ (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)


def _update_CPTR_EL3_Type_EZ (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)


def undefined_CPACR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_CPACR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_CPACR_Type_ASEDIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _update_CPACR_Type_ASEDIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _get_CPACR_Type_TRCDIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _update_CPACR_Type_TRCDIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _get_CPACR_Type_cp10 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 21 20)


def _update_CPACR_Type_cp10 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 20 x)


def _update_NSACR_Type_cp10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _get_NSACR_Type_cp10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _get_CPACR_Type_cp11 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 23 22)


def _update_CPACR_Type_cp11 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 22 x)


def _update_NSACR_Type_cp11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _get_NSACR_Type_cp11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)


def CPACR_read__1 (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CPACR ) : SailM CPACR_Type )
  let w__0 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def undefined_HCPTR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_HCPTR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_HCPTR_Type_TASE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _update_HCPTR_Type_TASE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _get_HCPTR_Type_TCP10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _update_HCPTR_Type_TCP10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _get_HCPTR_Type_TCP11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)


def _update_HCPTR_Type_TCP11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def HCPTR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HCPTR ) : SailM HCPTR_Type )
  let w__0 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def undefined_NSACR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_NSACR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_NSACR_Type_NSASEDIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _update_NSACR_Type_NSASEDIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _get_NSACR_Type_NSTRCDIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def _update_NSACR_Type_NSTRCDIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


/-- Type quantifiers: processorid : Int -/
def ClearExclusiveLocal (processorid : Int) : Unit :=
  ()


def DiscardTransactionalWrites (_ : Unit) : Unit :=
  ()


def ProcessorID (_ : Unit) : Int :=
  0


def CTI_SignalEvent (id : CrossTriggerIn) : Unit :=
  ()


def StopInstructionPrefetchAndEnableITR (_ : Unit) : Unit :=
  ()


def undefined_DBGOSDLR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_DBGOSDLR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_DBGOSDLR_Type_DLK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_DBGOSDLR_Type_DLK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_EDPRSR_Type_DLK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_OSDLR_EL1_Type_DLK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_EDPRSR_Type_DLK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_OSDLR_EL1_Type_DLK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def undefined_OSDLR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_OSDLR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def DBGOSDLR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DBGOSDLR ) : SailM DBGOSDLR_Type )
  let w__0 ← (( do readReg OSDLR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def undefined_DBGPRCR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_DBGPRCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_DBGPRCR_EL1_Type_CORENPDRQ (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_DBGPRCR_EL1_Type_CORENPDRQ (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_DBGPRCR_Type_CORENPDRQ (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_EDPRCR_Type_CORENPDRQ (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_DBGPRCR_Type_CORENPDRQ (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_EDPRCR_Type_CORENPDRQ (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def undefined_DBGPRCR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_DBGPRCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def DBGPRCR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DBGPRCR ) : SailM DBGPRCR_Type )
  let w__0 ← (( do readReg DBGPRCR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def CTI_SetEventLevel (id : CrossTriggerIn) (level : Signal) : Unit :=
  ()


def SetInterruptRequestLevel (intid : InterruptID) (level : Signal) : SailM Unit := do
  let w__1 ← (( do
    if (((BEq.beq level Signal_High) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do readReg __GIC_Active ) : SailM (Option InterruptID) )
        (pure (((bne w__0 (some intid)) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      writeReg __GIC_Pending (some intid))
  else (pure (()))


/-- Type quantifiers: k_M : Nat, N : Nat, k_M > N ∧ k_M ≥ 0 ∧ 0 ≤ (N - 1) -/
def Split (value_name : (BitVec k_M)) (N : Nat) : SailM ((BitVec (k_M - N)) × (BitVec N)) := do
  ArmFull.assert ((Sail.BitVec.length value_name) >b N) "sail-arm/v8_base.sail:8058.17-8058.18"
  (pure (((Sail.BitVec.castWidth (Sail.BitVec.extractLsb value_name
      (Sail.Int.toNatChecked (((Sail.BitVec.length value_name) -i 1))) N)), (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
      value_name (Sail.Int.toNatChecked ((N -i 1))) 0)))))


/-- Type quantifiers: k_round : Bool, shift : Int, value_name : Int -/
def RShr (value_name : Int) (shift : Int) (round : Bool) : SailM Int := do
  ArmFull.assert (shift >b 0) "sail-arm/v8_base.sail:8066.20-8066.21"
  (pure (if (round : Bool)
    then
      (Int.shiftr (value_name +i (Int.shiftl 1 (Sail.Int.toNatChecked ((shift -i 1)))))
        (Sail.Int.toNatChecked (shift)))
    else (Int.shiftr value_name (Sail.Int.toNatChecked (shift)))))


end ArmFull.Functions
