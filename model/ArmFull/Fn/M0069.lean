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

def _update_ICC_ASGI1R_EL1_Type_Aff1 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)


def _update_ICC_ASGI1R_Type_Aff1 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)


def _update_ICC_SGI0R_Type_Aff1 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)


def _update_ICC_SGI1R_EL1_Type_Aff1 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)


def _update_ICC_SGI1R_Type_Aff1 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)


def _update_MPIDR_EL1_Type_Aff1 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 8 x)


def _update_VMPIDR_EL2_Type_Aff1 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 8 x)


def _get_GITS_MPIDR_Type_Aff1 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)


def _get_ICC_ASGI1R_EL1_Type_Aff1 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)


def _get_ICC_ASGI1R_Type_Aff1 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)


def _get_ICC_SGI0R_Type_Aff1 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)


def _get_ICC_SGI1R_EL1_Type_Aff1 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)


def _get_ICC_SGI1R_Type_Aff1 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)


def _get_MPIDR_EL1_Type_Aff1 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)


def _get_MPIDR_Type_Aff1 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)


def _get_VMPIDR_EL2_Type_Aff1 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)


def _get_VMPIDR_Type_Aff1 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)


def _get_ICC_SGI0R_EL1_Type_Aff2 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)


def _update_ICC_SGI0R_EL1_Type_Aff2 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)


def _update_GITS_MPIDR_Type_Aff2 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 16 x)


def _update_ICC_ASGI1R_EL1_Type_Aff2 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)


def _update_ICC_ASGI1R_Type_Aff2 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)


def _update_ICC_SGI0R_Type_Aff2 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)


def _update_ICC_SGI1R_EL1_Type_Aff2 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)


def _update_ICC_SGI1R_Type_Aff2 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)


def _update_MPIDR_EL1_Type_Aff2 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)


def _update_VMPIDR_EL2_Type_Aff2 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)


def _get_GITS_MPIDR_Type_Aff2 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)


def _get_ICC_ASGI1R_EL1_Type_Aff2 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)


def _get_ICC_ASGI1R_Type_Aff2 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)


def _get_ICC_SGI0R_Type_Aff2 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)


def _get_ICC_SGI1R_EL1_Type_Aff2 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)


def _get_ICC_SGI1R_Type_Aff2 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)


def _get_MPIDR_EL1_Type_Aff2 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)


def _get_MPIDR_Type_Aff2 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)


def _get_VMPIDR_EL2_Type_Aff2 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)


def _get_VMPIDR_Type_Aff2 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)


def _get_ICC_SGI0R_EL1_Type_Aff3 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)


def _update_ICC_SGI0R_EL1_Type_Aff3 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)


def _update_GITS_MPIDR_Type_Aff3 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)


def _update_ICC_ASGI1R_EL1_Type_Aff3 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)


def _update_ICC_ASGI1R_Type_Aff3 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)


def _update_ICC_SGI0R_Type_Aff3 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)


def _update_ICC_SGI1R_EL1_Type_Aff3 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)


def _update_ICC_SGI1R_Type_Aff3 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)


def _update_MPIDR_EL1_Type_Aff3 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)


def _update_VMPIDR_EL2_Type_Aff3 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)


def _get_GITS_MPIDR_Type_Aff3 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)


def _get_ICC_ASGI1R_EL1_Type_Aff3 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)


def _get_ICC_ASGI1R_Type_Aff3 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)


def _get_ICC_SGI0R_Type_Aff3 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)


def _get_ICC_SGI1R_EL1_Type_Aff3 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)


def _get_ICC_SGI1R_Type_Aff3 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)


def _get_MPIDR_EL1_Type_Aff3 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)


def _get_VMPIDR_EL2_Type_Aff3 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)


def _get_ICC_SGI0R_EL1_Type_IRM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)


def _update_ICC_SGI0R_EL1_Type_IRM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)


def _update_ICC_ASGI1R_EL1_Type_IRM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)


def _update_ICC_ASGI1R_Type_IRM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)


def _update_ICC_SGI0R_Type_IRM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)


def _update_ICC_SGI1R_EL1_Type_IRM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)


def _update_ICC_SGI1R_Type_IRM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)


def _get_ICC_ASGI1R_EL1_Type_IRM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)


def _get_ICC_ASGI1R_Type_IRM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)


def _get_ICC_SGI0R_Type_IRM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)


def _get_ICC_SGI1R_EL1_Type_IRM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)


def _get_ICC_SGI1R_Type_IRM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)


def _get_ICC_SGI0R_EL1_Type_RS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)


def _update_ICC_SGI0R_EL1_Type_RS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)


def _update_ICC_ASGI1R_EL1_Type_RS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)


def _update_ICC_ASGI1R_Type_RS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)


def _update_ICC_SGI0R_Type_RS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)


def _update_ICC_SGI1R_EL1_Type_RS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)


def _update_ICC_SGI1R_Type_RS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)


def _get_ICC_ASGI1R_EL1_Type_RS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)


def _get_ICC_ASGI1R_Type_RS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)


def _get_ICC_SGI0R_Type_RS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)


def _get_ICC_SGI1R_EL1_Type_RS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)


def _get_ICC_SGI1R_Type_RS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)


def _get_ICC_SGI0R_EL1_Type_TargetList (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _update_ICC_SGI0R_EL1_Type_TargetList (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_ICC_ASGI1R_EL1_Type_TargetList (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_ICC_ASGI1R_Type_TargetList (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_ICC_SGI0R_Type_TargetList (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_ICC_SGI1R_EL1_Type_TargetList (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_ICC_SGI1R_Type_TargetList (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _get_ICC_ASGI1R_EL1_Type_TargetList (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _get_ICC_ASGI1R_Type_TargetList (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _get_ICC_SGI0R_Type_TargetList (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _get_ICC_SGI1R_EL1_Type_TargetList (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _get_ICC_SGI1R_Type_TargetList (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def __set_CNTHVS_CTL_EL2 (value_name : (BitVec 64)) : SailM Unit := do
  let r : CNTHVS_CTL_EL2_Type := value_name
  let w__0 ← (( do readReg CNTHVS_CTL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHVS_CTL_EL2 (Sail.BitVec.updateSubrange w__0 1 0 (BitVec.slice r 0 2))
  let w__1 ← (( do readReg CNTHVS_CTL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHVS_CTL_EL2 (Sail.BitVec.updateSubrange w__1 63 3 (BitVec.slice r 3 61))


def undefined_SPMACCESSR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_SPMACCESSR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_SPMACCESSR_EL1_Type_P31 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 63 62)


def _update_SPMACCESSR_EL1_Type_P31 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 62 x)


def _update_ICH_AP0R_EL2_Type_P31 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_ICH_AP0R_Type_P31 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_ICH_AP1R_EL2_Type_P31 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_ICH_AP1R_Type_P31 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_SPMACCESSR_EL2_Type_P31 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 62 x)


def _update_SPMACCESSR_EL3_Type_P31 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 62 x)


def _get_ICH_AP0R_EL2_Type_P31 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_ICH_AP0R_Type_P31 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_ICH_AP1R_EL2_Type_P31 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_ICH_AP1R_Type_P31 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_SPMACCESSR_EL2_Type_P31 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 63 62)


def _get_SPMACCESSR_EL3_Type_P31 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 63 62)


def Mk_SPMSELR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_SPMSELR_EL0_Type_SYSPMUSEL (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 9 4)


def _update_SPMSELR_EL0_Type_SYSPMUSEL (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 4 x)


def Mk_ID_AA64PFR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ID_AA64PFR1_EL1_Type_CSV2_frac (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)


def _update_ID_AA64PFR1_EL1_Type_CSV2_frac (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)


def _get_ID_AA64PFR1_EL1_Type_DF2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)


def _update_ID_AA64PFR1_EL1_Type_DF2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)


def _get_ID_AA64PFR1_EL1_Type_GCS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)


def _update_ID_AA64PFR1_EL1_Type_GCS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)


def _update_EDHSR_Type_GCS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)


def _get_EDHSR_Type_GCS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)


def _update_ID_AA64PFR1_EL1_Type_MPAM_frac (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_ID_AA64PFR1_EL1_Type_MTE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _update_ID_AA64PFR1_EL1_Type_MTE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_ID_AA64PFR1_EL1_Type_MTEX (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)


def _update_ID_AA64PFR1_EL1_Type_MTEX (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)


def _get_ID_AA64PFR1_EL1_Type_MTE_frac (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)


def _update_ID_AA64PFR1_EL1_Type_MTE_frac (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)


def _get_ID_AA64PFR1_EL1_Type_PFAR (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)


def _update_ID_AA64PFR1_EL1_Type_PFAR (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)


def _get_ID_AA64PFR1_EL1_Type_RAS_frac (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _update_ID_AA64PFR1_EL1_Type_RAS_frac (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _update_ID_PFR2_EL1_Type_RAS_frac (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _update_ID_PFR2_Type_RAS_frac (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_ID_PFR2_EL1_Type_RAS_frac (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _get_ID_PFR2_Type_RAS_frac (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _get_ID_AA64PFR1_EL1_Type_RNDR_trap (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _update_ID_AA64PFR1_EL1_Type_RNDR_trap (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _get_ID_AA64PFR1_EL1_Type_SME (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _update_ID_AA64PFR1_EL1_Type_SME (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _get_ID_AA64PFR1_EL1_Type_THE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)


def _update_ID_AA64PFR1_EL1_Type_THE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)


def Mk_ID_AA64PFR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ID_AA64PFR0_EL1_Type_AMU (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)


def _update_ID_AA64PFR0_EL1_Type_AMU (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)


def _update_EDPFR_Type_AMU (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)


def _update_ID_PFR0_EL1_Type_AMU (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _get_EDPFR_Type_AMU (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)


def _get_ID_PFR0_EL1_Type_AMU (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _get_ID_PFR0_Type_AMU (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _update_ID_AA64PFR0_EL1_Type_AdvSIMD (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _update_EDPFR_Type_AdvSIMD (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _get_EDPFR_Type_AdvSIMD (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _get_ID_AA64PFR0_EL1_Type_CSV2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)


def _update_ID_AA64PFR0_EL1_Type_CSV2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)


def _update_ID_PFR0_EL1_Type_CSV2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_ID_PFR0_EL1_Type_CSV2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_ID_PFR0_Type_CSV2 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_ID_AA64PFR0_EL1_Type_CSV3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)


def _update_ID_AA64PFR0_EL1_Type_CSV3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)


def _update_ID_PFR2_EL1_Type_CSV3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_ID_PFR2_Type_CSV3 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_ID_PFR2_EL1_Type_CSV3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_ID_PFR2_Type_CSV3 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_ID_AA64PFR0_EL1_Type_EL0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_EDPFR_Type_EL0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_EDPFR_Type_EL0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_ID_AA64PFR0_EL1_Type_EL1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_EDPFR_Type_EL1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_EDPFR_Type_EL1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_ID_AA64PFR0_EL1_Type_EL2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _update_EDAA32PFR_Type_EL2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _update_EDPFR_Type_EL2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_EDAA32PFR_Type_EL2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _get_EDPFR_Type_EL2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _update_ID_AA64PFR0_EL1_Type_EL3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _update_EDAA32PFR_Type_EL3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _update_EDPFR_Type_EL3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _get_EDAA32PFR_Type_EL3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _get_EDPFR_Type_EL3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _get_ID_AA64PFR0_EL1_Type_FP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_ID_AA64PFR0_EL1_Type_FP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_EDPFR_Type_FP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_EDPFR_Type_FP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_ID_AA64PFR0_EL1_Type_GIC (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _update_EDPFR_Type_GIC (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _update_ID_PFR1_EL1_Type_GIC (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _get_EDPFR_Type_GIC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_ID_PFR1_EL1_Type_GIC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _get_ID_PFR1_Type_GIC (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _update_ID_AA64PFR0_EL1_Type_MPAM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)


def _update_GITS_TYPER_Type_MPAM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)


def _get_GITS_TYPER_Type_MPAM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 38 38)


def _get_ID_AA64PFR0_EL1_Type_RAS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _update_ID_AA64PFR0_EL1_Type_RAS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _update_ID_PFR0_EL1_Type_RAS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _get_ID_PFR0_EL1_Type_RAS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _get_ID_PFR0_Type_RAS (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _get_ID_AA64PFR0_EL1_Type_RME (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)


def _update_ID_AA64PFR0_EL1_Type_RME (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)


end ArmFull.Functions
