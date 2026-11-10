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

def _update_MPAMVPMV_EL2_Type_VPM_V19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)


def _get_MPAMVPMV_EL2_Type_VPM_V2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_MPAMVPMV_EL2_Type_VPM_V2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_MPAMVPMV_EL2_Type_VPM_V20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def _update_MPAMVPMV_EL2_Type_VPM_V20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def _get_MPAMVPMV_EL2_Type_VPM_V21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


def _update_MPAMVPMV_EL2_Type_VPM_V21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)


def _get_MPAMVPMV_EL2_Type_VPM_V22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _update_MPAMVPMV_EL2_Type_VPM_V22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _get_MPAMVPMV_EL2_Type_VPM_V23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)


def _update_MPAMVPMV_EL2_Type_VPM_V23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)


def _get_MPAMVPMV_EL2_Type_VPM_V24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _update_MPAMVPMV_EL2_Type_VPM_V24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _get_MPAMVPMV_EL2_Type_VPM_V25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)


def _update_MPAMVPMV_EL2_Type_VPM_V25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)


def _get_MPAMVPMV_EL2_Type_VPM_V26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)


def _update_MPAMVPMV_EL2_Type_VPM_V26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)


def _get_MPAMVPMV_EL2_Type_VPM_V27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)


def _update_MPAMVPMV_EL2_Type_VPM_V27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)


def _get_MPAMVPMV_EL2_Type_VPM_V28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _update_MPAMVPMV_EL2_Type_VPM_V28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _get_MPAMVPMV_EL2_Type_VPM_V29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _update_MPAMVPMV_EL2_Type_VPM_V29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _get_MPAMVPMV_EL2_Type_VPM_V3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_MPAMVPMV_EL2_Type_VPM_V3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_MPAMVPMV_EL2_Type_VPM_V30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _update_MPAMVPMV_EL2_Type_VPM_V30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _get_MPAMVPMV_EL2_Type_VPM_V31 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _update_MPAMVPMV_EL2_Type_VPM_V31 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _get_MPAMVPMV_EL2_Type_VPM_V4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _update_MPAMVPMV_EL2_Type_VPM_V4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_MPAMVPMV_EL2_Type_VPM_V5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _update_MPAMVPMV_EL2_Type_VPM_V5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _get_MPAMVPMV_EL2_Type_VPM_V6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _update_MPAMVPMV_EL2_Type_VPM_V6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _get_MPAMVPMV_EL2_Type_VPM_V7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _update_MPAMVPMV_EL2_Type_VPM_V7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _get_MPAMVPMV_EL2_Type_VPM_V8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)


def _update_MPAMVPMV_EL2_Type_VPM_V8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)


def _get_MPAMVPMV_EL2_Type_VPM_V9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def _update_MPAMVPMV_EL2_Type_VPM_V9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


def undefined_MPAMVPM1_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MPAMVPM1_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_MPAMVPM1_EL2_Type_PhyPARTID4 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _update_MPAMVPM1_EL2_Type_PhyPARTID4 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _get_MPAMVPM1_EL2_Type_PhyPARTID5 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 31 16)


def _update_MPAMVPM1_EL2_Type_PhyPARTID5 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)


def _get_MPAMVPM1_EL2_Type_PhyPARTID6 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 47 32)


def _update_MPAMVPM1_EL2_Type_PhyPARTID6 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 32 x)


def _get_MPAMVPM1_EL2_Type_PhyPARTID7 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 63 48)


def _update_MPAMVPM1_EL2_Type_PhyPARTID7 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 48 x)


def undefined_MPAMVPM2_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MPAMVPM2_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_MPAMVPM2_EL2_Type_PhyPARTID10 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 47 32)


def _update_MPAMVPM2_EL2_Type_PhyPARTID10 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 32 x)


def _get_MPAMVPM2_EL2_Type_PhyPARTID11 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 63 48)


def _update_MPAMVPM2_EL2_Type_PhyPARTID11 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 48 x)


def _get_MPAMVPM2_EL2_Type_PhyPARTID8 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _update_MPAMVPM2_EL2_Type_PhyPARTID8 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _get_MPAMVPM2_EL2_Type_PhyPARTID9 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 31 16)


def _update_MPAMVPM2_EL2_Type_PhyPARTID9 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)


def undefined_MPAMVPM3_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MPAMVPM3_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_MPAMVPM3_EL2_Type_PhyPARTID12 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _update_MPAMVPM3_EL2_Type_PhyPARTID12 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _get_MPAMVPM3_EL2_Type_PhyPARTID13 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 31 16)


def _update_MPAMVPM3_EL2_Type_PhyPARTID13 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)


def _get_MPAMVPM3_EL2_Type_PhyPARTID14 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 47 32)


def _update_MPAMVPM3_EL2_Type_PhyPARTID14 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 32 x)


def _get_MPAMVPM3_EL2_Type_PhyPARTID15 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 63 48)


def _update_MPAMVPM3_EL2_Type_PhyPARTID15 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 48 x)


def undefined_MPAMVPM4_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MPAMVPM4_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_MPAMVPM4_EL2_Type_PhyPARTID16 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _update_MPAMVPM4_EL2_Type_PhyPARTID16 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _get_MPAMVPM4_EL2_Type_PhyPARTID17 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 31 16)


def _update_MPAMVPM4_EL2_Type_PhyPARTID17 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)


def _get_MPAMVPM4_EL2_Type_PhyPARTID18 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 47 32)


def _update_MPAMVPM4_EL2_Type_PhyPARTID18 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 32 x)


def _get_MPAMVPM4_EL2_Type_PhyPARTID19 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 63 48)


def _update_MPAMVPM4_EL2_Type_PhyPARTID19 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 48 x)


def undefined_MPAMVPM5_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MPAMVPM5_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_MPAMVPM5_EL2_Type_PhyPARTID20 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _update_MPAMVPM5_EL2_Type_PhyPARTID20 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _get_MPAMVPM5_EL2_Type_PhyPARTID21 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 31 16)


def _update_MPAMVPM5_EL2_Type_PhyPARTID21 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)


def _get_MPAMVPM5_EL2_Type_PhyPARTID22 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 47 32)


def _update_MPAMVPM5_EL2_Type_PhyPARTID22 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 32 x)


def _get_MPAMVPM5_EL2_Type_PhyPARTID23 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 63 48)


def _update_MPAMVPM5_EL2_Type_PhyPARTID23 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 48 x)


def undefined_MPAMVPM6_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MPAMVPM6_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_MPAMVPM6_EL2_Type_PhyPARTID24 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _update_MPAMVPM6_EL2_Type_PhyPARTID24 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _get_MPAMVPM6_EL2_Type_PhyPARTID25 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 31 16)


def _update_MPAMVPM6_EL2_Type_PhyPARTID25 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)


def _get_MPAMVPM6_EL2_Type_PhyPARTID26 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 47 32)


def _update_MPAMVPM6_EL2_Type_PhyPARTID26 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 32 x)


def _get_MPAMVPM6_EL2_Type_PhyPARTID27 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 63 48)


def _update_MPAMVPM6_EL2_Type_PhyPARTID27 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 48 x)


def undefined_MPAMVPM7_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MPAMVPM7_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_MPAMVPM7_EL2_Type_PhyPARTID28 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _update_MPAMVPM7_EL2_Type_PhyPARTID28 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _get_MPAMVPM7_EL2_Type_PhyPARTID29 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 31 16)


def _update_MPAMVPM7_EL2_Type_PhyPARTID29 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)


def _get_MPAMVPM7_EL2_Type_PhyPARTID30 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 47 32)


def _update_MPAMVPM7_EL2_Type_PhyPARTID30 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 32 x)


def _get_MPAMVPM7_EL2_Type_PhyPARTID31 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 63 48)


def _update_MPAMVPM7_EL2_Type_PhyPARTID31 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 48 x)


def undefined_MPAM0_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MPAM0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_MPAMSM_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MPAMSM_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def CPASAtPAS (pas : PASpace) : CachePASpace :=
  match pas with
  | .PAS_NonSecure => CPAS_NonSecure
  | .PAS_Secure => CPAS_Secure
  | .PAS_Root => CPAS_Root
  | .PAS_Realm => CPAS_Realm


def CPASAtSecurityState (ss : SecurityState) : CachePASpace :=
  match ss with
  | .SS_NonSecure => CPAS_NonSecure
  | .SS_Secure => CPAS_SecureNonSecure
  | .SS_Root => CPAS_Any
  | .SS_Realm => CPAS_RealmNonSecure


def undefined_CLIDR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CLIDR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_CLIDR_EL1_Type_Ctype1 (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)


def _update_CLIDR_EL1_Type_Ctype1 (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 0 x)


def _update_CLIDR_Type_Ctype1 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)


def _get_CLIDR_Type_Ctype1 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)


def _get_CLIDR_EL1_Type_Ctype2 (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 5 3)


def _update_CLIDR_EL1_Type_Ctype2 (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 3 x)


def _update_CLIDR_Type_Ctype2 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 3 x)


def _get_CLIDR_Type_Ctype2 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 5 3)


def _get_CLIDR_EL1_Type_Ctype3 (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 8 6)


def _update_CLIDR_EL1_Type_Ctype3 (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 6 x)


def _update_CLIDR_Type_Ctype3 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 6 x)


def _get_CLIDR_Type_Ctype3 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 8 6)


def _get_CLIDR_EL1_Type_Ctype4 (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 11 9)


def _update_CLIDR_EL1_Type_Ctype4 (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 9 x)


def _update_CLIDR_Type_Ctype4 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 9 x)


def _get_CLIDR_Type_Ctype4 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 11 9)


def _get_CLIDR_EL1_Type_Ctype5 (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 14 12)


def _update_CLIDR_EL1_Type_Ctype5 (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 12 x)


def _update_CLIDR_Type_Ctype5 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 12 x)


def _get_CLIDR_Type_Ctype5 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 14 12)


def _get_CLIDR_EL1_Type_Ctype6 (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 17 15)


def _update_CLIDR_EL1_Type_Ctype6 (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 15 x)


def _update_CLIDR_Type_Ctype6 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 15 x)


def _get_CLIDR_Type_Ctype6 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 17 15)


def _get_CLIDR_EL1_Type_Ctype7 (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 20 18)


def _update_CLIDR_EL1_Type_Ctype7 (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 18 x)


def _update_CLIDR_Type_Ctype7 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 18 x)


def _get_CLIDR_Type_Ctype7 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 20 18)


def _get_CLIDR_EL1_Type_ICB (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 32 30)


def _update_CLIDR_EL1_Type_ICB (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 30 x)


def _update_CLIDR_Type_ICB (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 30 x)


def _get_CLIDR_Type_ICB (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 31 30)


def _get_CLIDR_EL1_Type_LoC (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 26 24)


def _update_CLIDR_EL1_Type_LoC (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 24 x)


def _update_CLIDR_Type_LoC (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 24 x)


def _get_CLIDR_Type_LoC (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 26 24)


def _get_CLIDR_EL1_Type_LoUIS (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 23 21)


def _update_CLIDR_EL1_Type_LoUIS (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 21 x)


def _update_CLIDR_Type_LoUIS (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 21 x)


def _get_CLIDR_Type_LoUIS (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 23 21)


def _get_CLIDR_EL1_Type_LoUU (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 29 27)


def _update_CLIDR_EL1_Type_LoUU (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 27 x)


def _update_CLIDR_Type_LoUU (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 27 x)


def _get_CLIDR_Type_LoUU (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 29 27)


def _get_CLIDR_EL1_Type_Ttype1 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 34 33)


def _update_CLIDR_EL1_Type_Ttype1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 33 x)


def _get_CLIDR_EL1_Type_Ttype2 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 36 35)


def _update_CLIDR_EL1_Type_Ttype2 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 35 x)


def _get_CLIDR_EL1_Type_Ttype3 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 38 37)


def _update_CLIDR_EL1_Type_Ttype3 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 37 x)


def _get_CLIDR_EL1_Type_Ttype4 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 40 39)


def _update_CLIDR_EL1_Type_Ttype4 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 39 x)


def _get_CLIDR_EL1_Type_Ttype5 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 42 41)


def _update_CLIDR_EL1_Type_Ttype5 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 41 x)


def _get_CLIDR_EL1_Type_Ttype6 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 44 43)


def _update_CLIDR_EL1_Type_Ttype6 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 43 x)


def _get_CLIDR_EL1_Type_Ttype7 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 46 45)


def _update_CLIDR_EL1_Type_Ttype7 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 45 x)


/-- Type quantifiers: level : Int -/
def GetCacheInfo (level : Int) (cachetype : CacheType) : SailM (Int × Int × Int) := do
  let w__0 ← (( do (undefined_int_at (← occLabel 773) ()) ) : SailM Int )
  let w__1 ← (( do (undefined_int_at (← occLabel 774) ()) ) : SailM Int )
  let w__2 ← (( do (undefined_int_at (← occLabel 775) ()) ) : SailM Int )
  (pure (((w__0, w__1, w__2) : (Int × Int × Int))))


def AESShiftRows (op : (BitVec 128)) : (BitVec 128) :=
  ((((((((((((((((Sail.BitVec.extractLsb op 95 88) +++ (Sail.BitVec.extractLsb op 55 48)) +++ (Sail.BitVec.extractLsb
                                op 15 8)) +++ (Sail.BitVec.extractLsb op 103 96)) +++ (Sail.BitVec.extractLsb
                            op 63 56)) +++ (Sail.BitVec.extractLsb op 23 16)) +++ (Sail.BitVec.extractLsb
                        op 111 104)) +++ (Sail.BitVec.extractLsb op 71 64)) +++ (Sail.BitVec.extractLsb
                    op 31 24)) +++ (Sail.BitVec.extractLsb op 119 112)) +++ (Sail.BitVec.extractLsb
                op 79 72)) +++ (Sail.BitVec.extractLsb op 39 32)) +++ (Sail.BitVec.extractLsb op 127
            120)) +++ (Sail.BitVec.extractLsb op 87 80)) +++ (Sail.BitVec.extractLsb op 47 40)) +++ (Sail.BitVec.extractLsb
      op 7 0))


def AESInvShiftRows (op : (BitVec 128)) : (BitVec 128) :=
  ((((((((((((((((Sail.BitVec.extractLsb op 31 24) +++ (Sail.BitVec.extractLsb op 55 48)) +++ (Sail.BitVec.extractLsb
                                op 79 72)) +++ (Sail.BitVec.extractLsb op 103 96)) +++ (Sail.BitVec.extractLsb
                            op 127 120)) +++ (Sail.BitVec.extractLsb op 23 16)) +++ (Sail.BitVec.extractLsb
                        op 47 40)) +++ (Sail.BitVec.extractLsb op 71 64)) +++ (Sail.BitVec.extractLsb
                    op 95 88)) +++ (Sail.BitVec.extractLsb op 119 112)) +++ (Sail.BitVec.extractLsb
                op 15 8)) +++ (Sail.BitVec.extractLsb op 39 32)) +++ (Sail.BitVec.extractLsb op 63
            56)) +++ (Sail.BitVec.extractLsb op 87 80)) +++ (Sail.BitVec.extractLsb op 111 104)) +++ (Sail.BitVec.extractLsb
      op 7 0))


def FFmul02 (b : (BitVec 8)) : (BitVec 8) :=
  let FFmul_02 : (BitVec 2048) :=
    (((((((((((((((0xE5E7E1E3EDEFE9EBF5F7F1F3FDFFF9FB#128 +++ 0xC5C7C1C3CDCFC9CBD5D7D1D3DDDFD9DB#128) +++ 0xA5A7A1A3ADAFA9ABB5B7B1B3BDBFB9BB#128) +++ 0x858781838D8F898B959791939D9F999B#128) +++ 0x656761636D6F696B757771737D7F797B#128) +++ 0x454741434D4F494B555751535D5F595B#128) +++ 0x252721232D2F292B353731333D3F393B#128) +++ 0x050701030D0F090B151711131D1F191B#128) +++ 0xFEFCFAF8F6F4F2F0EEECEAE8E6E4E2E0#128) +++ 0xDEDCDAD8D6D4D2D0CECCCAC8C6C4C2C0#128) +++ 0xBEBCBAB8B6B4B2B0AEACAAA8A6A4A2A0#128) +++ 0x9E9C9A98969492908E8C8A8886848280#128) +++ 0x7E7C7A78767472706E6C6A6866646260#128) +++ 0x5E5C5A58565452504E4C4A4846444240#128) +++ 0x3E3C3A38363432302E2C2A2826242220#128) +++ 0x1E1C1A18161412100E0C0A0806040200#128)
  (BitVec.slice FFmul_02 (Sail.Int.toNatChecked (((BitVec.toNat b) *i 8))) 8)


def FFmul03 (b : (BitVec 8)) : (BitVec 8) :=
  let FFmul_03 : (BitVec 2048) :=
    (((((((((((((((0x1A191C1F16151013020104070E0D080B#128 +++ 0x2A292C2F26252023323134373E3D383B#128) +++ 0x7A797C7F76757073626164676E6D686B#128) +++ 0x4A494C4F46454043525154575E5D585B#128) +++ 0xDAD9DCDFD6D5D0D3C2C1C4C7CECDC8CB#128) +++ 0xEAE9ECEFE6E5E0E3F2F1F4F7FEFDF8FB#128) +++ 0xBAB9BCBFB6B5B0B3A2A1A4A7AEADA8AB#128) +++ 0x8A898C8F86858083929194979E9D989B#128) +++ 0x818287848D8E8B88999A9F9C95969390#128) +++ 0xB1B2B7B4BDBEBBB8A9AAAFACA5A6A3A0#128) +++ 0xE1E2E7E4EDEEEBE8F9FAFFFCF5F6F3F0#128) +++ 0xD1D2D7D4DDDEDBD8C9CACFCCC5C6C3C0#128) +++ 0x414247444D4E4B48595A5F5C55565350#128) +++ 0x717277747D7E7B78696A6F6C65666360#128) +++ 0x212227242D2E2B28393A3F3C35363330#128) +++ 0x111217141D1E1B18090A0F0C05060300#128)
  (BitVec.slice FFmul_03 (Sail.Int.toNatChecked (((BitVec.toNat b) *i 8))) 8)


def FFmul09 (b : (BitVec 8)) : (BitVec 8) :=
  let FFmul_09 : (BitVec 2048) :=
    (((((((((((((((0x464F545D626B70790E071C152A233831#128 +++ 0xD6DFC4CDF2FBE0E99E978C85BAB3A8A1#128) +++ 0x7D746F6659504B42353C272E1118030A#128) +++ 0xEDE4FFF6C9C0DBD2A5ACB7BE8188939A#128) +++ 0x3039222B141D060F78716A635C554E47#128) +++ 0xA0A9B2BB848D969FE8E1FAF3CCC5DED7#128) +++ 0x0B0219102F263D34434A5158676E757C#128) +++ 0x9B928980BFB6ADA4D3DAC1C8F7FEE5EC#128) +++ 0xAAA3B8B18E879C95E2EBF0F9C6CFD4DD#128) +++ 0x3A3328211E170C05727B6069565F444D#128) +++ 0x9198838AB5BCA7AED9D0CBC2FDF4EFE6#128) +++ 0x0108131A252C373E49405B526D647F76#128) +++ 0xDCD5CEC7F8F1EAE3949D868FB0B9A2AB#128) +++ 0x4C455E5768617A73040D161F2029323B#128) +++ 0xE7EEF5FCC3CAD1D8AFA6BDB48B829990#128) +++ 0x777E656C535A41483F362D241B120900#128)
  (BitVec.slice FFmul_09 (Sail.Int.toNatChecked (((BitVec.toNat b) *i 8))) 8)


def FFmul0B (b : (BitVec 8)) : (BitVec 8) :=
  let FFmul_0B : (BitVec 2048) :=
    (((((((((((((((0xA3A8B5BE8F849992FBF0EDE6D7DCC1CA#128 +++ 0x1318050E3F3429224B405D56676C717A#128) +++ 0xD8D3CEC5F4FFE2E9808B969DACA7BAB1#128) +++ 0x68637E75444F5259303B262D1C170A01#128) +++ 0x555E434879726F640D061B10212A373C#128) +++ 0xE5EEF3F8C9C2DFD4BDB6ABA0919A878C#128) +++ 0x2E2538330209141F767D606B5A514C47#128) +++ 0x9E958883B2B9A4AFC6CDD0DBEAE1FCF7#128) +++ 0x545F424978736E650C071A11202B363D#128) +++ 0xE4EFF2F9C8C3DED5BCB7AAA1909B868D#128) +++ 0x2F2439320308151E777C616A5B504D46#128) +++ 0x9F948982B3B8A5AEC7CCD1DAEBE0FDF6#128) +++ 0xA2A9B4BF8E859893FAF1ECE7D6DDC0CB#128) +++ 0x1219040F3E3528234A415C57666D707B#128) +++ 0xD9D2CFC4F5FEE3E8818A979CADA6BBB0#128) +++ 0x69627F74454E5358313A272C1D160B00#128)
  (BitVec.slice FFmul_0B (Sail.Int.toNatChecked (((BitVec.toNat b) *i 8))) 8)


def FFmul0D (b : (BitVec 8)) : (BitVec 8) :=
  let FFmul_0D : (BitVec 2048) :=
    (((((((((((((((0x979A8D80A3AEB9B4FFF2E5E8CBC6D1DC#128 +++ 0x474A5D50737E69642F2235381B16010C#128) +++ 0x2C21363B1815020F44495E53707D6A67#128) +++ 0xFCF1E6EBC8C5D2DF94998E83A0ADBAB7#128) +++ 0xFAF7E0EDCEC3D4D9929F8885A6ABBCB1#128) +++ 0x2A27303D1E130409424F5855767B6C61#128) +++ 0x414C5B5675786F622924333E1D10070A#128) +++ 0x919C8B86A5A8BFB2F9F4E3EECDC0D7DA#128) +++ 0x4D40575A7974636E25283F32111C0B06#128) +++ 0x9D90878AA9A4B3BEF5F8EFE2C1CCDBD6#128) +++ 0xF6FBECE1C2CFD8D59E938489AAA7B0BD#128) +++ 0x262B3C31121F08054E4354597A77606D#128) +++ 0x202D3A3714190E034845525F7C71666B#128) +++ 0xF0FDEAE7C4C9DED39895828FACA1B6BB#128) +++ 0x9B96818CAFA2B5B8F3FEE9E4C7CADDD0#128) +++ 0x4B46515C7F726568232E3934171A0D00#128)
  (BitVec.slice FFmul_0D (Sail.Int.toNatChecked (((BitVec.toNat b) *i 8))) 8)


def FFmul0E (b : (BitVec 8)) : (BitVec 8) :=
  let FFmul_0E : (BitVec 2048) :=
    (((((((((((((((0x8D83919FB5BBA9A7FDF3E1EFC5CBD9D7#128 +++ 0x6D63717F555B49471D13010F252B3937#128) +++ 0x56584A446E60727C26283A341E10020C#128) +++ 0xB6B8AAA48E80929CC6C8DAD4FEF0E2EC#128) +++ 0x202E3C321816040A505E4C426866747A#128) +++ 0xC0CEDCD2F8F6E4EAB0BEACA28886949A#128) +++ 0xFBF5E7E9C3CDDFD18B859799B3BDAFA1#128) +++ 0x1B150709232D3F316B657779535D4F41#128) +++ 0xCCC2D0DEF4FAE8E6BCB2A0AE848A9896#128) +++ 0x2C22303E141A08065C52404E646A7876#128) +++ 0x17190B052F21333D67697B755F51434D#128) +++ 0xF7F9EBE5CFC1D3DD87899B95BFB1A3AD#128) +++ 0x616F7D735957454B111F0D032927353B#128) +++ 0x818F9D93B9B7A5ABF1FFEDE3C9C7D5DB#128) +++ 0xBAB4A6A8828C9E90CAC4D6D8F2FCEEE0#128) +++ 0x5A544648626C7E702A243638121C0E00#128)
  (BitVec.slice FFmul_0E (Sail.Int.toNatChecked (((BitVec.toNat b) *i 8))) 8)


def SHAchoose (x : (BitVec 32)) (y : (BitVec 32)) (z : (BitVec 32)) : (BitVec 32) :=
  (((y ^^^ z) &&& x) ^^^ z)


def SHAparity (x : (BitVec 32)) (y : (BitVec 32)) (z : (BitVec 32)) : (BitVec 32) :=
  ((x ^^^ y) ^^^ z)


end ArmFull.Functions
