module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork set_option backward.proofsInPublic true @[expose] public section

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

def _update_MPAMVPMV_EL2_Type_VPM_V11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _get_MPAMVPMV_EL2_Type_VPM_V12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _update_MPAMVPMV_EL2_Type_VPM_V12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _get_MPAMVPMV_EL2_Type_VPM_V13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _update_MPAMVPMV_EL2_Type_VPM_V13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _get_MPAMVPMV_EL2_Type_VPM_V14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _update_MPAMVPMV_EL2_Type_VPM_V14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _get_MPAMVPMV_EL2_Type_VPM_V15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _update_MPAMVPMV_EL2_Type_VPM_V15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _get_MPAMVPMV_EL2_Type_VPM_V16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _update_MPAMVPMV_EL2_Type_VPM_V16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _get_MPAMVPMV_EL2_Type_VPM_V17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _update_MPAMVPMV_EL2_Type_VPM_V17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _get_MPAMVPMV_EL2_Type_VPM_V18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)


def _update_MPAMVPMV_EL2_Type_VPM_V18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)


def _get_MPAMVPMV_EL2_Type_VPM_V19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)


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


end ArmFull.Functions
