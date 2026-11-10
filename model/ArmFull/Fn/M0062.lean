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

def _update_PRRR_Type_TR7 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def MAIR0_S_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _MAIR0_S ) : SailM MAIR0_Type )
  let w__0 ← (( do readReg PRRR_S ) : SailM (BitVec 32) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def undefined_MAIR1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_MAIR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_NMRR_Type_IR0 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)


def _update_NMRR_Type_IR0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 0 x)


def _get_NMRR_Type_IR1 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 3 2)


def _update_NMRR_Type_IR1 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 2 x)


def _get_NMRR_Type_IR2 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)


def _update_NMRR_Type_IR2 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 4 x)


def _get_NMRR_Type_IR3 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)


def _update_NMRR_Type_IR3 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 6 x)


def _get_NMRR_Type_IR4 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 9 8)


def _update_NMRR_Type_IR4 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 8 x)


def _get_NMRR_Type_IR5 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)


def _update_NMRR_Type_IR5 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 10 x)


def _get_NMRR_Type_IR6 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 13 12)


def _update_NMRR_Type_IR6 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 12 x)


def _get_NMRR_Type_IR7 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _update_NMRR_Type_IR7 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _get_NMRR_Type_OR0 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 17 16)


def _update_NMRR_Type_OR0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 16 x)


def _get_NMRR_Type_OR1 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 19 18)


def _update_NMRR_Type_OR1 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 18 x)


def _get_NMRR_Type_OR2 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 21 20)


def _update_NMRR_Type_OR2 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 20 x)


def _get_NMRR_Type_OR3 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 23 22)


def _update_NMRR_Type_OR3 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 22 x)


def _get_NMRR_Type_OR4 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)


def _update_NMRR_Type_OR4 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 24 x)


def _get_NMRR_Type_OR5 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 27 26)


def _update_NMRR_Type_OR5 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 26 x)


def _get_NMRR_Type_OR6 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 29 28)


def _update_NMRR_Type_OR6 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 28 x)


def _get_NMRR_Type_OR7 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 31 30)


def _update_NMRR_Type_OR7 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 30 x)


def MAIR1_S_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _MAIR1_S ) : SailM MAIR1_Type )
  let w__0 ← (( do readReg NMRR_S ) : SailM (BitVec 32) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def undefined_HMAIR0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_HMAIR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def HMAIR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HMAIR0 ) : SailM HMAIR0_Type )
  let w__0 ← (( do readReg MAIR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def undefined_HMAIR1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_HMAIR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def HMAIR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HMAIR1 ) : SailM HMAIR1_Type )
  let w__0 ← (( do readReg MAIR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 32 32)) : (BitVec 32))
  (pure (r))


/-- Type quantifiers: k_aligned : Bool -/
def AArch32_S1HasAlignmentFault (accdesc : AccessDescriptor) (aligned : Bool) (ntlsmd : (BitVec 1)) (memattrs : MemoryAttributes) : Bool :=
  if ((BEq.beq accdesc.acctype AccessType_IFETCH) : Bool)
  then false
  else
    (if ((accdesc.a32lsmd && (ntlsmd == 0#1)) : Bool)
    then ((BEq.beq memattrs.memtype MemType_Device) && (bne memattrs.device DeviceType_GRE))
    else
      (if ((BEq.beq accdesc.acctype AccessType_DCZero) : Bool)
      then (BEq.beq memattrs.memtype MemType_Device)
      else ((BEq.beq memattrs.memtype MemType_Device) && (! aligned))))


def AArch32_S2IASize (t0sz : (BitVec 4)) : Int :=
  (32 -i (BitVec.toInt t0sz))


/-- Type quantifiers: k_aligned : Bool -/
def AArch32_S2HasAlignmentFault (accdesc : AccessDescriptor) (aligned : Bool) (memattrs : MemoryAttributes) : Bool :=
  if ((BEq.beq accdesc.acctype AccessType_IFETCH) : Bool)
  then false
  else
    (if ((BEq.beq accdesc.acctype AccessType_DCZero) : Bool)
    then (BEq.beq memattrs.memtype MemType_Device)
    else ((BEq.beq memattrs.memtype MemType_Device) && (! aligned)))


def AArch32_S2StartLevel (sl0 : (BitVec 2)) : Int :=
  (2 -i (BitVec.toNat sl0))


def Mk_DACR32_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_DACR32_EL2_Type_D0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)


def _update_DACR32_EL2_Type_D0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 0 x)


def _update_DACR_Type_D0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 0 x)


def _get_DACR_Type_D0 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)


def _get_DACR32_EL2_Type_D1 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 3 2)


def _update_DACR32_EL2_Type_D1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 2 x)


def _update_DACR_Type_D1 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 2 x)


def _get_DACR_Type_D1 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 3 2)


def _get_DACR32_EL2_Type_D10 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 21 20)


def _update_DACR32_EL2_Type_D10 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 20 x)


def _update_DACR_Type_D10 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 20 x)


def _get_DACR_Type_D10 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 21 20)


def _get_DACR32_EL2_Type_D11 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 23 22)


def _update_DACR32_EL2_Type_D11 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 22 x)


def _update_DACR_Type_D11 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 22 x)


def _get_DACR_Type_D11 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 23 22)


def _get_DACR32_EL2_Type_D12 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)


def _update_DACR32_EL2_Type_D12 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 24 x)


def _update_DACR_Type_D12 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 24 x)


def _get_DACR_Type_D12 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)


def _get_DACR32_EL2_Type_D13 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 27 26)


def _update_DACR32_EL2_Type_D13 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 26 x)


def _update_DACR_Type_D13 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 26 x)


def _get_DACR_Type_D13 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 27 26)


def _get_DACR32_EL2_Type_D14 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 29 28)


def _update_DACR32_EL2_Type_D14 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 28 x)


def _update_DACR_Type_D14 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 28 x)


def _get_DACR_Type_D14 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 29 28)


def _get_DACR32_EL2_Type_D15 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 31 30)


def _update_DACR32_EL2_Type_D15 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 30 x)


def _update_DACR_Type_D15 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 30 x)


def _get_DACR_Type_D15 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 31 30)


def _get_DACR32_EL2_Type_D2 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)


def _update_DACR32_EL2_Type_D2 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 4 x)


def _update_DACR_Type_D2 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 4 x)


def _get_DACR_Type_D2 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)


def _get_DACR32_EL2_Type_D3 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)


def _update_DACR32_EL2_Type_D3 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)


def _update_DACR_Type_D3 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 6 x)


def _get_DACR_Type_D3 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)


def _get_DACR32_EL2_Type_D4 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 9 8)


def _update_DACR32_EL2_Type_D4 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 8 x)


def _update_DACR_Type_D4 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 8 x)


def _get_DACR_Type_D4 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 9 8)


def _get_DACR32_EL2_Type_D5 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)


def _update_DACR32_EL2_Type_D5 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)


def _update_DACR_Type_D5 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 10 x)


def _get_DACR_Type_D5 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)


def _get_DACR32_EL2_Type_D6 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 13 12)


def _update_DACR32_EL2_Type_D6 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 12 x)


def _update_DACR_Type_D6 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 12 x)


def _get_DACR_Type_D6 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 13 12)


def _get_DACR32_EL2_Type_D7 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _update_DACR32_EL2_Type_D7 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _update_DACR_Type_D7 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _get_DACR_Type_D7 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _get_DACR32_EL2_Type_D8 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 17 16)


def _update_DACR32_EL2_Type_D8 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 16 x)


def _update_DACR_Type_D8 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 16 x)


def _get_DACR_Type_D8 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 17 16)


def _get_DACR32_EL2_Type_D9 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 19 18)


def _update_DACR32_EL2_Type_D9 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 18 x)


def _update_DACR_Type_D9 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 18 x)


def _get_DACR_Type_D9 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 19 18)


def undefined_DACR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_DACR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def DACR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DACR_NS ) : SailM DACR_Type )
  let w__0 ← (( do readReg DACR32_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


/-- Type quantifiers: level : Int -/
def AArch32_DecodeDescriptorTypeSD (descriptor : (BitVec 32)) (level : Int) : SDFType :=
  if (((level == 1) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb descriptor 1 0)) == 0b01#2)) : Bool)
  then SDFType_Table
  else
    (if (((level == 1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 18)])) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 descriptor 1)]))) == 0b01#2)) : Bool)
    then SDFType_Section
    else
      (if (((level == 1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 18)])) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   descriptor 1)]))) == 0b11#2)) : Bool)
      then SDFType_Supersection
      else
        (if (((level == 2) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb descriptor 1
                 0)) == 0b01#2)) : Bool)
        then SDFType_LargePage
        else
          (if (((level == 2) && (let b__0 := (Sail.BitVec.extractLsb descriptor 1 0)
               (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 1 1)) == (1#1 : (BitVec 1))) : Bool)
               then true
               else false : Bool))) : Bool)
          then SDFType_SmallPage
          else SDFType_Invalid))))


def AArch32_TranslationSizeSD (sdftype : SDFType) : Int :=
  let tsize : Int := 12
  let tsize : Int :=
    match sdftype with
    | .SDFType_SmallPage => 12
    | .SDFType_LargePage => 16
    | .SDFType_Section => 20
    | .SDFType_Supersection => 24
    | _ => tsize
  let tsize : Int := tsize
  tsize


def _get_PAR_Type_ATTR (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 63 56)


def _update_PAR_Type_ATTR (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 56 x)


def _update_PAR_EL1_Type_ATTR (v : (BitVec 128)) (x : (BitVec 8)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 63 56 x)


def _get_PAR_EL1_Type_ATTR (v : (BitVec 128)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 63 56)


def _get_PAR_Type_FST (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 6 1)


def _update_PAR_Type_FST (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 1 x)


def _update_PAR_EL1_Type_FST (v : (BitVec 128)) (x : (BitVec 6)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 6 1 x)


def _get_PAR_EL1_Type_FST (v : (BitVec 128)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 6 1)


def _get_PAR_Type_FSTAGE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def _update_PAR_Type_FSTAGE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


def _get_PAR_Type_Inner (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 6 4)


def _update_PAR_Type_Inner (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 4 x)


def _get_PAR_Type_Outer (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 3 2)


def _update_PAR_Type_Outer (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 2 x)


def _get_PAR_Type_S2WLK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)


def _update_PAR_Type_S2WLK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)


def _get_PAR_EL1_Type_TopLevel (v : (BitVec 128)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _update_PAR_EL1_Type_TopLevel (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def Mk_CTILSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_CTILSR_Type_SLI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_CTILSR_Type_SLI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_EDLSR_Type_SLI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_PMLSR_Type_SLI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_EDLSR_Type_SLI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_PMLSR_Type_SLI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_CTILSR_Type_SLK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_CTILSR_Type_SLK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_EDLSR_Type_SLK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_PMLSR_Type_SLK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_EDLSR_Type_SLK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_PMLSR_Type_SLK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def Mk_EDLSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PMLSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def undefined_DBGDTR_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_DBGDTR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_DBGDTR_EL0_Type_HighWord (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 63 32)


def _update_DBGDTR_EL0_Type_HighWord (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 32 x)


def _get_DBGDTR_EL0_Type_LowWord (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def _update_DBGDTR_EL0_Type_LowWord (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def Mk_EDPRSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_EDPRSR_Type_HALTED (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _update_EDPRSR_Type_HALTED (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_EDPRSR_Type_PU (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_EDPRSR_Type_PU (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_EDPRSR_Type_R (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_EDPRSR_Type_R (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_EDPRSR_Type_SDAD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)


def _update_EDPRSR_Type_SDAD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)


def _get_EDPRSR_Type_SDR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)


def _update_EDPRSR_Type_SDR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _get_EDPRSR_Type_SPMAD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _update_EDPRSR_Type_SPMAD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _get_EDPRSR_Type_SR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_EDPRSR_Type_SR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_GICM_TYPER_Type_SR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _get_GICM_TYPER_Type_SR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _get_DBGDCCINT_Type_RX (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _update_MDCCINT_EL1_Type_RX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _get_MDCCINT_EL1_Type_RX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_DBGDCCINT_Type_TX (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _update_MDCCINT_EL1_Type_TX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _get_MDCCINT_EL1_Type_TX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def Mk_MDCCINT_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


end ArmFull.Functions
