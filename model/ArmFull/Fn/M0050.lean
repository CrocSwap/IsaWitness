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

def Mk_RGSR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_RGSR_EL1_Type_SEED (v : (BitVec 64)) : (BitVec 48) :=
  (Sail.BitVec.extractLsb v 55 8)


def _update_RGSR_EL1_Type_SEED (v : (BitVec 64)) (x : (BitVec 48)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 8 x)


def _get_RGSR_EL1_Type_TAG (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_RGSR_EL1_Type_TAG (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def AArch64_CanonicalTagCheck (memaddrdesc : AddressDescriptor) (ptag : (BitVec 4)) : Bool :=
  let expected_tag : (BitVec 4) :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access memaddrdesc.vaddress 55)])) == 0#1) : Bool)
    then 0b0000#4
    else 0b1111#4
  (ptag == expected_tag)


def AArch64_PhysicalTag (vaddr : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb vaddr 59 56)


def undefined_TFSRE0_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_TFSRE0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_TFSRE0_EL1_Type_TF0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_TFSRE0_EL1_Type_TF0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_TFSR_EL1_Type_TF0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_TFSR_EL2_Type_TF0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_TFSR_EL3_Type_TF0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_TFSR_EL1_Type_TF0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_TFSR_EL2_Type_TF0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_TFSR_EL3_Type_TF0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_TFSRE0_EL1_Type_TF1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_TFSRE0_EL1_Type_TF1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_TFSR_EL1_Type_TF1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_TFSR_EL2_Type_TF1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_TFSR_EL1_Type_TF1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_TFSR_EL2_Type_TF1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def undefined_TFSR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_TFSR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_TFSR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_TFSR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_TFSR_EL3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_TFSR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_CONTEXTIDR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CONTEXTIDR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_DBGBCR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_DBGBCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_DBGBCR_EL1_Type_BAS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 8 5)


def _update_DBGBCR_EL1_Type_BAS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 5 x)


def _update_DBGBCR_Type_BAS (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 5 x)


def _update_DBGWCR_EL1_Type_BAS (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 5 x)


def _update_DBGWCR_Type_BAS (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 5 x)


def _get_DBGBCR_Type_BAS (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 8 5)


def _get_DBGWCR_EL1_Type_BAS (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 12 5)


def _get_DBGWCR_Type_BAS (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 12 5)


def _get_DBGBCR_EL1_Type_BT2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_DBGBCR_EL1_Type_BT2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_DBGBCR_EL1_Type_HMC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _update_DBGBCR_EL1_Type_HMC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _update_DBGBCR_Type_HMC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _update_DBGWCR_EL1_Type_HMC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _update_DBGWCR_Type_HMC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _get_DBGBCR_Type_HMC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _get_DBGWCR_EL1_Type_HMC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _get_DBGWCR_Type_HMC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _get_DBGBCR_EL1_Type_LBN (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_DBGBCR_EL1_Type_LBN (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_DBGBCR_Type_LBN (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_DBGWCR_EL1_Type_LBN (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_DBGWCR_Type_LBN (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_DBGBCR_Type_LBN (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_DBGWCR_EL1_Type_LBN (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_DBGWCR_Type_LBN (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_DBGBCR_EL1_Type_LBNX (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 31 30)


def _update_DBGBCR_EL1_Type_LBNX (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 30 x)


def _update_DBGWCR_EL1_Type_LBNX (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 30 x)


def _get_DBGWCR_EL1_Type_LBNX (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 31 30)


def _get_DBGBCR_EL1_Type_MASK (v : (BitVec 64)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 28 24)


def _update_DBGBCR_EL1_Type_MASK (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 24 x)


def _update_DBGWCR_EL1_Type_MASK (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 24 x)


def _update_DBGWCR_Type_MASK (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 24 x)


def _get_DBGWCR_EL1_Type_MASK (v : (BitVec 64)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 28 24)


def _get_DBGWCR_Type_MASK (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 28 24)


def _get_DBGBCR_EL1_Type_PMC (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 2 1)


def _update_DBGBCR_EL1_Type_PMC (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 1 x)


def _update_DBGBCR_Type_PMC (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 1 x)


def _get_DBGBCR_Type_PMC (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 2 1)


def _get_DBGBCR_EL1_Type_SSC (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _update_DBGBCR_EL1_Type_SSC (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _update_DBGBCR_Type_SSC (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _update_DBGWCR_EL1_Type_SSC (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _update_DBGWCR_Type_SSC (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _get_DBGBCR_Type_SSC (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _get_DBGWCR_EL1_Type_SSC (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _get_DBGWCR_Type_SSC (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _get_DBGBCR_EL1_Type_SSCE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _update_DBGBCR_EL1_Type_SSCE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _update_DBGWCR_EL1_Type_SSCE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _get_DBGWCR_EL1_Type_SSCE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def undefined_DBGBVR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_DBGBVR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_DBGBVR_EL1_Type_ContextID (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def _update_DBGBVR_EL1_Type_ContextID (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def _update_DBGBVR_Type_ContextID (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def _get_DBGBVR_Type_ContextID (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def _get_DBGBVR_EL1_Type_ContextID2 (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 63 32)


def _update_DBGBVR_EL1_Type_ContextID2 (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 32 x)


def _update_DBGBXVR_Type_ContextID2 (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def _get_DBGBXVR_Type_ContextID2 (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def _get_DBGBVR_EL1_Type_RESS (v : (BitVec 64)) : (BitVec 15) :=
  ((Sail.BitVec.extractLsb v 63 57) +++ ((Sail.BitVec.extractLsb v 56 53) +++ (Sail.BitVec.extractLsb
        v 52 49)))


def _update_DBGBVR_EL1_Type_RESS (v : (BitVec 64)) (x : (BitVec 15)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange
      (Sail.BitVec.updateSubrange v 63 57
        (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((15 -i 1)))
          (Sail.Int.toNatChecked ((((15 -i 1) -i ((63 -i 57) +i 1)) +i 1))))) 56 53
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((15 -i 1) -i ((63 -i 57) +i 1))))
        (Sail.Int.toNatChecked (((((15 -i 1) -i ((63 -i 57) +i 1)) -i ((56 -i 53) +i 1)) +i 1)))))
    52 49
    (Sail.BitVec.extractLsb x
      (Sail.Int.toNatChecked ((((15 -i 1) -i ((63 -i 57) +i 1)) -i ((56 -i 53) +i 1))))
      (Sail.Int.toNatChecked ((((((15 -i 1) -i ((63 -i 57) +i 1)) -i ((56 -i 53) +i 1)) -i ((52 -i 49) +i 1)) +i 1)))))


def _update_DBGWVR_EL1_Type_RESS (v : (BitVec 64)) (x : (BitVec 15)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange
      (Sail.BitVec.updateSubrange v 63 57
        (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((15 -i 1)))
          (Sail.Int.toNatChecked ((((15 -i 1) -i ((63 -i 57) +i 1)) +i 1))))) 56 53
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((15 -i 1) -i ((63 -i 57) +i 1))))
        (Sail.Int.toNatChecked (((((15 -i 1) -i ((63 -i 57) +i 1)) -i ((56 -i 53) +i 1)) +i 1)))))
    52 49
    (Sail.BitVec.extractLsb x
      (Sail.Int.toNatChecked ((((15 -i 1) -i ((63 -i 57) +i 1)) -i ((56 -i 53) +i 1))))
      (Sail.Int.toNatChecked ((((((15 -i 1) -i ((63 -i 57) +i 1)) -i ((56 -i 53) +i 1)) -i ((52 -i 49) +i 1)) +i 1)))))


def _update_VNCR_EL2_Type_RESS (v : (BitVec 64)) (x : (BitVec 7)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 57 x)


def _get_DBGWVR_EL1_Type_RESS (v : (BitVec 64)) : (BitVec 15) :=
  ((Sail.BitVec.extractLsb v 63 57) +++ ((Sail.BitVec.extractLsb v 56 53) +++ (Sail.BitVec.extractLsb
        v 52 49)))


def _get_VNCR_EL2_Type_RESS (v : (BitVec 64)) : (BitVec 7) :=
  (Sail.BitVec.extractLsb v 63 57)


def _get_DBGBVR_EL1_Type_VMID (v : (BitVec 64)) : (BitVec 16) :=
  ((Sail.BitVec.extractLsb v 47 40) +++ (Sail.BitVec.extractLsb v 39 32))


def _update_DBGBVR_EL1_Type_VMID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 47 40
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((16 -i 1)))
        (Sail.Int.toNatChecked ((((16 -i 1) -i ((47 -i 40) +i 1)) +i 1))))) 39 32
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((16 -i 1) -i ((47 -i 40) +i 1))))
      (Sail.Int.toNatChecked (((((16 -i 1) -i ((47 -i 40) +i 1)) -i ((39 -i 32) +i 1)) +i 1)))))


def _update_DBGBXVR_Type_VMID (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 15 8
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((16 -i 1)))
        (Sail.Int.toNatChecked ((((16 -i 1) -i ((15 -i 8) +i 1)) +i 1))))) 7 0
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((16 -i 1) -i ((15 -i 8) +i 1))))
      (Sail.Int.toNatChecked (((((16 -i 1) -i ((15 -i 8) +i 1)) -i ((7 -i 0) +i 1)) +i 1)))))


def _update_EDVIDSR_Type_VMID (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 15 8
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((16 -i 1)))
        (Sail.Int.toNatChecked ((((16 -i 1) -i ((15 -i 8) +i 1)) +i 1))))) 7 0
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((16 -i 1) -i ((15 -i 8) +i 1))))
      (Sail.Int.toNatChecked (((((16 -i 1) -i ((15 -i 8) +i 1)) -i ((7 -i 0) +i 1)) +i 1)))))


def _update_PMVCIDSR_Type_VMID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 47 40
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((16 -i 1)))
        (Sail.Int.toNatChecked ((((16 -i 1) -i ((47 -i 40) +i 1)) +i 1))))) 39 32
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((16 -i 1) -i ((47 -i 40) +i 1))))
      (Sail.Int.toNatChecked (((((16 -i 1) -i ((47 -i 40) +i 1)) -i ((39 -i 32) +i 1)) +i 1)))))


def _update_PMVIDSR_Type_VMID (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 15 8
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((16 -i 1)))
        (Sail.Int.toNatChecked ((((16 -i 1) -i ((15 -i 8) +i 1)) +i 1))))) 7 0
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((16 -i 1) -i ((15 -i 8) +i 1))))
      (Sail.Int.toNatChecked (((((16 -i 1) -i ((15 -i 8) +i 1)) -i ((7 -i 0) +i 1)) +i 1)))))


def _update_VTTBR_EL2_Type_VMID (v : (BitVec 128)) (x : (BitVec 16)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 63 48 x)


def _update_VTTBR_Type_VMID (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)


def _get_DBGBXVR_Type_VMID (v : (BitVec 32)) : (BitVec 16) :=
  ((Sail.BitVec.extractLsb v 15 8) +++ (Sail.BitVec.extractLsb v 7 0))


def _get_EDVIDSR_Type_VMID (v : (BitVec 32)) : (BitVec 16) :=
  ((Sail.BitVec.extractLsb v 15 8) +++ (Sail.BitVec.extractLsb v 7 0))


def _get_PMVCIDSR_Type_VMID (v : (BitVec 64)) : (BitVec 16) :=
  ((Sail.BitVec.extractLsb v 47 40) +++ (Sail.BitVec.extractLsb v 39 32))


def _get_PMVIDSR_Type_VMID (v : (BitVec 32)) : (BitVec 16) :=
  ((Sail.BitVec.extractLsb v 15 8) +++ (Sail.BitVec.extractLsb v 7 0))


def _get_VTTBR_EL2_Type_VMID (v : (BitVec 128)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 63 48)


def _get_VTTBR_Type_VMID (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)


def undefined_EDSCR2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_EDSCR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def EDSCR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _EDSCR2 ) : SailM EDSCR2_Type )
  let w__0 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 32 32)) : (BitVec 32))
  (pure (r))


def undefined_VTCR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_VTCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_VTCR_EL2_Type_GCSH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)


def _update_VTCR_EL2_Type_GCSH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)


def _get_VTCR_EL2_Type_NSA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _update_VTCR_EL2_Type_NSA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _get_VTCR_EL2_Type_NSW (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _update_VTCR_EL2_Type_NSW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _get_VTCR_EL2_Type_S2PIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 36 36)


def _update_VTCR_EL2_Type_S2PIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)


def _update_ID_AA64MMFR3_EL1_Type_S2PIE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _get_ID_AA64MMFR3_EL1_Type_S2PIE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _get_VTCR_EL2_Type_S2POE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)


def _update_VTCR_EL2_Type_S2POE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)


def _update_ID_AA64MMFR3_EL1_Type_S2POE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _get_ID_AA64MMFR3_EL1_Type_S2POE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _get_VTCR_EL2_Type_SL0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)


def _update_VTCR_EL2_Type_SL0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)


def _update_VSTCR_EL2_Type_SL0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)


def _update_VTCR_Type_SL0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 6 x)


def _get_VSTCR_EL2_Type_SL0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)


def _get_VTCR_Type_SL0 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)


def _get_VTCR_EL2_Type_SL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)


def _update_VTCR_EL2_Type_SL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)


def _update_VSTCR_EL2_Type_SL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)


def _get_VSTCR_EL2_Type_SL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)


def _get_VTCR_EL2_Type_TL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 41 41)


def _update_VTCR_EL2_Type_TL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 41 x)


def _get_VTCR_EL2_Type_TL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 35 35)


def _update_VTCR_EL2_Type_TL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 35 x)


def _get_VTCR_EL2_Type_VS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)


def _update_VTCR_EL2_Type_VS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)


def undefined_VTTBR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_VTTBR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_VTTBR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 128) := do
  (undefined_bitvector_at (ℓ.child 0) 128)


def Mk_VTTBR_EL2_Type (v : (BitVec 128)) : (BitVec 128) :=
  v


def VTTBR_EL2_read (_ : Unit) : SailM (BitVec 128) := do
  let r ← (( do readReg _VTTBR_EL2 ) : SailM VTTBR_EL2_Type )
  let w__0 ← (( do readReg VTTBR ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 63 0 (BitVec.slice w__0 0 64)) : (BitVec 128))
  (pure (r))


def undefined_DBGWCR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_DBGWCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_DBGWCR_EL1_Type_LSC (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 4 3)


def _update_DBGWCR_EL1_Type_LSC (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 3 x)


def _update_DBGWCR_Type_LSC (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 3 x)


def _get_DBGWCR_Type_LSC (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 4 3)


def _get_DBGWCR_EL1_Type_PAC (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 2 1)


def _update_DBGWCR_EL1_Type_PAC (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 1 x)


def _update_DBGWCR_Type_PAC (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 1 x)


def _get_DBGWCR_Type_PAC (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 2 1)


def _get_DBGWCR_EL1_Type_WT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def _update_DBGWCR_EL1_Type_WT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def _update_DBGWCR_Type_WT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def _update_PMCFGR_Type_WT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)


def _get_DBGWCR_Type_WT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def _get_PMCFGR_Type_WT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)


def undefined_DBGWVR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_DBGWVR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def gic_readonly (offset : (BitVec 16)) : Unit :=
  (prerr_bits "[GIC] Write to RO offset: " offset)


/-- Type quantifiers: n : Nat, n > 0 -/
def __WriteUART (offset : (BitVec 16)) (n : Nat) (data : (BitVec (8 * n))) : Unit :=
  match offset with
  | 0x0000 => (putchar (BitVec.toNat (Sail.BitVec.extractLsb data 7 0)))
  | _ =>
    (let _ : Unit := (prerr_bits "[UART] Unknown write offset: " offset)
    (prerr_bits "[UART] Unknown write data: " data))


def undefined_POR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_POR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_POR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_POR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_POR_EL3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


end ArmFull.Functions
