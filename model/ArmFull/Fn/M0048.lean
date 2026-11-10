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

def FPEXC_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : FPEXC_Type := value_name
  let w__0 ← (( do readReg FPEXC32_EL2 ) : SailM (BitVec 64) )
  writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _FPEXC r


def SetAccumulatedFPExceptions (accumulated_exceptions : (BitVec 8)) : Unit :=
  ()


def IsFault (addrdesc : AddressDescriptor) : Bool :=
  (bne addrdesc.fault.statuscode Fault_None)


def IsFault__1 (fault : Fault) : Bool :=
  (bne fault Fault_None)


def IsFault__2 (retstatus : PhysMemRetStatus) : Bool :=
  (bne retstatus.statuscode Fault_None)


def undefined_CNTHP_CTL_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CNTHP_CTL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_CNTHP_CTL_EL2_Type_ENABLE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_CNTHP_CTL_EL2_Type_ENABLE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_CNTHPS_CTL_EL2_Type_ENABLE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_CNTHPS_CTL_Type_ENABLE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_CNTHP_CTL_Type_ENABLE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_CNTHVS_CTL_EL2_Type_ENABLE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_CNTHVS_CTL_Type_ENABLE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_CNTHV_CTL_EL2_Type_ENABLE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_CNTHV_CTL_Type_ENABLE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_CNTPS_CTL_EL1_Type_ENABLE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_CNTP_CTL_EL0_Type_ENABLE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_CNTP_CTL_Type_ENABLE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_CNTV_CTL_EL0_Type_ENABLE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_CNTV_CTL_Type_ENABLE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_CNTHPS_CTL_EL2_Type_ENABLE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_CNTHPS_CTL_Type_ENABLE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_CNTHP_CTL_Type_ENABLE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_CNTHVS_CTL_EL2_Type_ENABLE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_CNTHVS_CTL_Type_ENABLE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_CNTHV_CTL_EL2_Type_ENABLE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_CNTHV_CTL_Type_ENABLE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_CNTPS_CTL_EL1_Type_ENABLE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_CNTP_CTL_EL0_Type_ENABLE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_CNTP_CTL_Type_ENABLE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_CNTV_CTL_EL0_Type_ENABLE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_CNTV_CTL_Type_ENABLE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_CNTHP_CTL_EL2_Type_IMASK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_CNTHP_CTL_EL2_Type_IMASK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_CNTHPS_CTL_EL2_Type_IMASK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_CNTHPS_CTL_Type_IMASK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_CNTHP_CTL_Type_IMASK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_CNTHVS_CTL_EL2_Type_IMASK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_CNTHVS_CTL_Type_IMASK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_CNTHV_CTL_EL2_Type_IMASK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_CNTHV_CTL_Type_IMASK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_CNTPS_CTL_EL1_Type_IMASK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_CNTP_CTL_EL0_Type_IMASK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_CNTP_CTL_Type_IMASK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_CNTV_CTL_EL0_Type_IMASK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_CNTV_CTL_Type_IMASK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_CNTHPS_CTL_EL2_Type_IMASK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_CNTHPS_CTL_Type_IMASK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_CNTHP_CTL_Type_IMASK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_CNTHVS_CTL_EL2_Type_IMASK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_CNTHVS_CTL_Type_IMASK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_CNTHV_CTL_EL2_Type_IMASK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_CNTHV_CTL_Type_IMASK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_CNTPS_CTL_EL1_Type_IMASK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_CNTP_CTL_EL0_Type_IMASK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_CNTP_CTL_Type_IMASK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_CNTV_CTL_EL0_Type_IMASK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_CNTV_CTL_Type_IMASK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_CNTHP_CTL_EL2_Type_ISTATUS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_CNTHP_CTL_EL2_Type_ISTATUS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_CNTHPS_CTL_EL2_Type_ISTATUS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_CNTHPS_CTL_Type_ISTATUS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_CNTHP_CTL_Type_ISTATUS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_CNTHVS_CTL_EL2_Type_ISTATUS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_CNTHVS_CTL_Type_ISTATUS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_CNTHV_CTL_EL2_Type_ISTATUS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_CNTHV_CTL_Type_ISTATUS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_CNTPS_CTL_EL1_Type_ISTATUS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_CNTP_CTL_EL0_Type_ISTATUS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_CNTP_CTL_Type_ISTATUS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_CNTV_CTL_EL0_Type_ISTATUS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_CNTV_CTL_Type_ISTATUS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_CNTHPS_CTL_EL2_Type_ISTATUS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_CNTHPS_CTL_Type_ISTATUS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_CNTHP_CTL_Type_ISTATUS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_CNTHVS_CTL_EL2_Type_ISTATUS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_CNTHVS_CTL_Type_ISTATUS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_CNTHV_CTL_EL2_Type_ISTATUS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_CNTHV_CTL_Type_ISTATUS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_CNTPS_CTL_EL1_Type_ISTATUS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_CNTP_CTL_EL0_Type_ISTATUS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_CNTP_CTL_Type_ISTATUS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_CNTV_CTL_EL0_Type_ISTATUS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_CNTV_CTL_Type_ISTATUS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def undefined_CNTHP_CTL_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_CNTHP_CTL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def CNTHP_CTL_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CNTHP_CTL ) : SailM CNTHP_CTL_Type )
  let w__0 ← (( do readReg CNTHP_CTL_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def CNTHP_CTL_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTHP_CTL_Type := value_name
  let w__0 ← (( do readReg CNTHP_CTL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHP_CTL_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _CNTHP_CTL r


def undefined_CNTHP_CVAL_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CNTHP_CVAL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_CNTHP_CVAL_EL2_Type_CompareValue (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)


def _update_CNTHP_CVAL_EL2_Type_CompareValue (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)


def _update_CNTHPS_CVAL_EL2_Type_CompareValue (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)


def _update_CNTHP_CVAL_Type_CompareValue (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)


def _update_CNTHVS_CVAL_EL2_Type_CompareValue (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)


def _update_CNTHV_CVAL_EL2_Type_CompareValue (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)


def _update_CNTPS_CVAL_EL1_Type_CompareValue (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)


def _update_CNTP_CVAL_EL0_Type_CompareValue (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)


def _update_CNTP_CVAL_Type_CompareValue (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)


def _update_CNTV_CVAL_EL0_Type_CompareValue (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)


def _update_CNTV_CVAL_Type_CompareValue (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)


def _get_CNTHPS_CVAL_EL2_Type_CompareValue (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)


def _get_CNTHP_CVAL_Type_CompareValue (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)


def _get_CNTHVS_CVAL_EL2_Type_CompareValue (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)


def _get_CNTHV_CVAL_EL2_Type_CompareValue (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)


def _get_CNTPS_CVAL_EL1_Type_CompareValue (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)


def _get_CNTP_CVAL_EL0_Type_CompareValue (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)


def _get_CNTP_CVAL_Type_CompareValue (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)


def _get_CNTV_CVAL_EL0_Type_CompareValue (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)


def _get_CNTV_CVAL_Type_CompareValue (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)


def undefined_CNTHP_CVAL_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CNTHP_CVAL_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def CNTHP_CVAL_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _CNTHP_CVAL ) : SailM CNTHP_CVAL_Type )
  let w__0 ← (( do readReg CNTHP_CVAL_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 63 0 (BitVec.slice w__0 0 64)) : (BitVec 64))
  (pure (r))


def undefined_CNTP_CTL_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CNTP_CTL_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_CNTP_CTL_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_CNTP_CTL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def CNTP_CTL_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CNTP_CTL_NS ) : SailM CNTP_CTL_Type )
  let w__0 ← (( do readReg CNTP_CTL_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def CNTP_CTL_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTP_CTL_Type := value_name
  let w__0 ← (( do readReg CNTP_CTL_EL0 ) : SailM (BitVec 64) )
  writeReg CNTP_CTL_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _CNTP_CTL_NS r


def undefined_CNTP_CVAL_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CNTP_CVAL_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_CNTP_CVAL_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CNTP_CVAL_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def CNTP_CVAL_NS_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _CNTP_CVAL_NS ) : SailM CNTP_CVAL_Type )
  let w__0 ← (( do readReg CNTP_CVAL_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 63 0 (BitVec.slice w__0 0 64)) : (BitVec 64))
  (pure (r))


def undefined_CNTV_CTL_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CNTV_CTL_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_CNTV_CVAL_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CNTV_CVAL_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_CNTHPS_CTL_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CNTHPS_CTL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_CNTHPS_CVAL_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CNTHPS_CVAL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_CNTHVS_CTL_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CNTHVS_CTL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_CNTHVS_CVAL_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CNTHVS_CVAL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_CNTHV_CTL_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CNTHV_CTL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_CNTHV_CVAL_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CNTHV_CVAL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_CNTPS_CTL_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CNTPS_CTL_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_CNTPS_CVAL_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CNTPS_CVAL_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_CNTCR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_CNTCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_CNTCR_Type_FCREQ (v : (BitVec 32)) : (BitVec 10) :=
  (Sail.BitVec.extractLsb v 17 8)


def _update_CNTCR_Type_FCREQ (v : (BitVec 32)) (x : (BitVec 10)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 8 x)


def _get_CNTCR_Type_HDBG (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_CNTCR_Type_HDBG (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_AMCFGR_EL0_Type_HDBG (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _update_AMCFGR_Type_HDBG (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _update_AMCR_EL0_Type_HDBG (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _update_AMCR_Type_HDBG (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _get_AMCFGR_EL0_Type_HDBG (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _get_AMCFGR_Type_HDBG (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _get_AMCR_EL0_Type_HDBG (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _get_AMCR_Type_HDBG (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _get_CNTCR_Type_SCEN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_CNTCR_Type_SCEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def undefined_CNTSCR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_CNTSCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_CNTSCR_Type_ScaleVal (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def _update_CNTSCR_Type_ScaleVal (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def SetEventRegister (_ : Unit) : SailM Unit := do
  writeReg EventRegister 1#1
  (wakeup_request ())


def undefined_CNTKCTL_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CNTKCTL_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def C47PickALUEXCEPTIONRETURN (_ : Unit) : SailM Constraint := do
  let rank ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 1189) 0 1))) ) :
    SailM Nat )
  (pure (if ((rank == 0) : Bool)
    then Constraint_NOP
    else Constraint_UNDEF))


def C47PickBASEOVERLAP (_ : Unit) : SailM Constraint := do
  let rank ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 1190) 0 2))) ) :
    SailM Nat )
  (pure (if ((rank == 0) : Bool)
    then Constraint_NOP
    else
      (if ((rank == 1) : Bool)
      then Constraint_UNDEF
      else Constraint_UNKNOWN)))


def C47PickBPNOTCTXCMP (_ : Unit) : SailM Constraint := do
  let rank ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 1191) 0 2))) ) :
    SailM Nat )
  (pure (if ((rank == 0) : Bool)
    then Constraint_DISABLED
    else
      (if ((rank == 1) : Bool)
      then Constraint_NONE
      else Constraint_UNKNOWN)))


def C47PickBPNOTIMPL (_ : Unit) : SailM Constraint := do
  let rank ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 1192) 0 1))) ) :
    SailM Nat )
  (pure (if ((rank == 0) : Bool)
    then Constraint_DISABLED
    else Constraint_UNKNOWN))


def C47PickDATAOVERLAP (_ : Unit) : SailM Constraint := do
  let rank ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 1193) 0 2))) ) :
    SailM Nat )
  (pure (if ((rank == 0) : Bool)
    then Constraint_NOP
    else
      (if ((rank == 1) : Bool)
      then Constraint_UNDEF
      else Constraint_UNKNOWN)))


def C47PickDEVICETAGSTORE (_ : Unit) : SailM Constraint := do
  let rank ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 1194) 0 1))) ) :
    SailM Nat )
  (pure (if ((rank == 0) : Bool)
    then Constraint_FAULT
    else Constraint_NONE))


def C47PickDEVPAGE2 (_ : Unit) : SailM Constraint := do
  let rank ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 1195) 0 1))) ) :
    SailM Nat )
  (pure (if ((rank == 0) : Bool)
    then Constraint_FAULT
    else Constraint_NONE))


def C47PickINSTRDEVICE (_ : Unit) : SailM Constraint := do
  let rank ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 1196) 0 1))) ) :
    SailM Nat )
  (pure (if ((rank == 0) : Bool)
    then Constraint_FAULT
    else Constraint_NONE))


def C47PickLDPOVERLAP (_ : Unit) : SailM Constraint := do
  let rank ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 1197) 0 2))) ) :
    SailM Nat )
  (pure (if ((rank == 0) : Bool)
    then Constraint_NOP
    else
      (if ((rank == 1) : Bool)
      then Constraint_UNDEF
      else Constraint_UNKNOWN)))


end ArmFull.Functions
