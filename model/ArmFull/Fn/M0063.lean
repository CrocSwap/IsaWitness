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

def DLR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DLR ) : SailM DLR_Type )
  let w__0 ← (( do readReg DLR_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def DSPSR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DSPSR ) : SailM DSPSR_Type )
  let w__0 ← (( do readReg DSPSR_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def Mk_CTIDEVCTL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_EDVIDSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_EDVIDSR_Type_CONTEXTIDR_EL2 (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def _update_EDVIDSR_Type_CONTEXTIDR_EL2 (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def _get_EDVIDSR_Type_HV (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _update_EDVIDSR_Type_HV (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def Mk_PMPCSR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_PMPCSR_Type_PCSample (v : (BitVec 64)) : (BitVec 56) :=
  ((Sail.BitVec.extractLsb v 55 32) +++ (Sail.BitVec.extractLsb v 31 0))


def _update_PMPCSR_Type_PCSample (v : (BitVec 64)) (x : (BitVec 56)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 55 32
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((56 -i 1)))
        (Sail.Int.toNatChecked ((((56 -i 1) -i ((55 -i 32) +i 1)) +i 1))))) 31 0
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((56 -i 1) -i ((55 -i 32) +i 1))))
      (Sail.Int.toNatChecked (((((56 -i 1) -i ((55 -i 32) +i 1)) -i ((31 -i 0) +i 1)) +i 1)))))


def _update_DBGDEVID_Type_PCSample (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_EDDEVID_Type_PCSample (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_PMDEVID_Type_PCSample (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_DBGDEVID_Type_PCSample (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_EDDEVID_Type_PCSample (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_PMDEVID_Type_PCSample (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def Mk_PMVIDSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_HTRFCR_Type_E0HTRE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_TRFCR_EL2_Type_E0HTRE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_TRFCR_EL2_Type_E0HTRE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_HTRFCR_Type_E2TRE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_TRFCR_EL2_Type_E2TRE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_TRFCR_EL2_Type_E2TRE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def Mk_TRFCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_TRFCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_TRFCR_EL1_Type_E0TRE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_TRFCR_EL1_Type_E0TRE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_TRFCR_Type_E0TRE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_TRFCR_EL1_Type_E1TRE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_TRFCR_EL1_Type_E1TRE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_TRFCR_Type_E1TRE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def TraceSynchronizationBarrier (_ : Unit) : Unit :=
  ()


/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV81 (enabled : Bool) : SailM Unit := do
  writeReg v8Ap1_IMPLEMENTED enabled


/-- Type quantifiers: value_name : Int -/
def decode_max_smeveclen (value_name : Int) : SailM Int := do
  let svl : Int := (Int.shiftr value_name 1)
  let bitpos : Int := 0
  let (bitpos, svl) ← (( do
    let loop_vars ← sailWhileFuelM (fuel := 1048576) (fun (bitpos, svl) => (pure (svl != 0))) (bitpos, svl)
      fun (bitpos, svl) => do
        (pure (let svl : Int := (Int.shiftr svl 1)
          let bitpos : Int := (bitpos +i 1)
          (bitpos, svl) : (Int × Int)))
    (pure loop_vars) ) : SailM (Int × Int) )
  let bitpos : Int :=
    if (((value_name == 0) || ((bitpos >b 4) : Bool)) : Bool)
    then 2
    else bitpos
  let bitpos : Int := bitpos
  let max_svl : Nat := (Sail.Int.toNatChecked ((128 *i (2 ^i bitpos))))
  (pure (max_svl))


def undefined_DBGBCR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_DBGBCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def DBGBCR_read (n : Nat) : SailM (BitVec 32) := do
  let w__0 ← (( do readReg _DBGBCR ) : SailM (Vector (BitVec 32) 16) )
  let r : DBGBCR_Type := (GetElem?.getElem! w__0 n)
  let w__1 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
  let r :=
    ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! w__1 n) 0 32)) : (BitVec 32))
  (pure (r))


def undefined_DBGBVR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_DBGBVR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def DBGBVR_read (n : Nat) : SailM (BitVec 32) := do
  let w__0 ← (( do readReg _DBGBVR ) : SailM (Vector (BitVec 32) 16) )
  let r : DBGBVR_Type := (GetElem?.getElem! w__0 n)
  let w__1 ← (( do readReg DBGBVR_EL1 ) : SailM (Vector (BitVec 64) 64) )
  let r :=
    ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! w__1 n) 0 32)) : (BitVec 32))
  (pure (r))


def undefined_DBGBXVR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_DBGBXVR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def DBGBXVR_read (n : Nat) : SailM (BitVec 32) := do
  let w__0 ← (( do readReg _DBGBXVR ) : SailM (Vector (BitVec 32) 16) )
  let r : DBGBXVR_Type := (GetElem?.getElem! w__0 n)
  let w__1 ← (( do readReg DBGBVR_EL1 ) : SailM (Vector (BitVec 64) 64) )
  let r :=
    ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! w__1 n) 32 32)) : (BitVec 32))
  (pure (r))


def Mk_DBGVCR32_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_DBGVCR32_EL2_Type_NSD (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _update_DBGVCR32_EL2_Type_NSD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_DBGVCR_Type_NSD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _get_DBGVCR_Type_NSD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_DBGVCR32_EL2_Type_NSF (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _update_DBGVCR32_EL2_Type_NSF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_DBGVCR_Type_NSF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _get_DBGVCR_Type_NSF (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_DBGVCR32_EL2_Type_NSI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _update_DBGVCR32_EL2_Type_NSI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_DBGVCR_Type_NSI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _get_DBGVCR_Type_NSI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_DBGVCR32_EL2_Type_NSP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)


def _update_DBGVCR32_EL2_Type_NSP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)


def _update_DBGVCR_Type_NSP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)


def _get_DBGVCR_Type_NSP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)


def _get_DBGVCR32_EL2_Type_NSS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)


def _update_DBGVCR32_EL2_Type_NSS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)


def _update_DBGVCR_Type_NSS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)


def _get_DBGVCR_Type_NSS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)


def _get_DBGVCR32_EL2_Type_SD (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _update_DBGVCR32_EL2_Type_SD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _update_DBGVCR_Type_SD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_DBGVCR_Type_SD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _get_DBGVCR32_EL2_Type_SF (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _update_DBGVCR32_EL2_Type_SF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _update_DBGVCR_Type_SF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _get_DBGVCR_Type_SF (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _get_DBGVCR32_EL2_Type_SI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _update_DBGVCR32_EL2_Type_SI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_DBGVCR_Type_SI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _get_DBGVCR_Type_SI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_DBGVCR32_EL2_Type_SP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_DBGVCR32_EL2_Type_SP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_DBGVCR_Type_SP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_DBGVCR_Type_SP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_DBGVCR32_EL2_Type_SU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_DBGVCR32_EL2_Type_SU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_DBGVCR_Type_SU (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_DBGVCR_Type_SU (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_DBGVCR_Type_MD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _update_DBGVCR_Type_MD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _get_DBGVCR_Type_MF (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _update_DBGVCR_Type_MF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _get_DBGVCR_Type_MI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _update_DBGVCR_Type_MI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _get_DBGVCR_Type_MP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)


def _update_DBGVCR_Type_MP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _get_DBGVCR_Type_MS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _update_DBGVCR_Type_MS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def undefined_DBGWCR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_DBGWCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def DBGWCR_read (n : Nat) : SailM (BitVec 32) := do
  let w__0 ← (( do readReg _DBGWCR ) : SailM (Vector (BitVec 32) 16) )
  let r : DBGWCR_Type := (GetElem?.getElem! w__0 n)
  let w__1 ← (( do readReg DBGWCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
  let r :=
    ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! w__1 n) 0 32)) : (BitVec 32))
  (pure (r))


def undefined_DBGWVR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_DBGWVR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def DBGWVR_read (n : Nat) : SailM (BitVec 32) := do
  let w__0 ← (( do readReg _DBGWVR ) : SailM (Vector (BitVec 32) 16) )
  let r : DBGWVR_Type := (GetElem?.getElem! w__0 n)
  let w__1 ← (( do readReg DBGWVR_EL1 ) : SailM (Vector (BitVec 64) 64) )
  let r :=
    ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! w__1 n) 0 32)) : (BitVec 32))
  (pure (r))


/-- Type quantifiers: processorid : Int, size : Int -/
def AArch32_MarkExclusiveVA (address : (BitVec 32)) (processorid : Int) (size : Int) : Unit :=
  ()


/-- Type quantifiers: n : Int -/
def Din_read (n : Int) : SailM (BitVec 64) := do
  ArmFull.assert ((n ≥b 0) && (n ≤b 31)) "sail-arm/v8_base.sail:42439.27-42439.28"
  let w__0 ← (( do readReg _Dclone ) : SailM (Vector (BitVec 64) 32) )
  (pure ((GetElem?.getElem! w__0 (Sail.Int.toNatChecked (n)))))


def LastInITBlock (_ : Unit) : SailM Bool := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  (pure (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb w__0.IT 3 0)) == 0b1000#4)))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 31 -/
def PMEVCNTR_read (n : Nat) : SailM (BitVec 32) := do
  let w__0 ← (( do readReg _PMEVCNTR ) : SailM (Vector (BitVec 32) 31) )
  let r : PMEVCNTR_Type := (GetElem?.getElem! w__0 n)
  let w__1 ← (( do readReg PMEVCNTR_EL0 ) : SailM (Vector (BitVec 64) 32) )
  let r :=
    ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! w__1 n) 0 32)) : (BitVec 32))
  (pure (r))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 31 -/
def PMEVCNTR_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMEVCNTR_Type := value_name
  let w__0 ← (( do readReg PMEVCNTR_EL0 ) : SailM (Vector (BitVec 64) 32) )
  let w__1 ← (( do readReg PMEVCNTR_EL0 ) : SailM (Vector (BitVec 64) 32) )
  writeReg PMEVCNTR_EL0 (vectorUpdate w__0 n
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__1 n) 31 0 (BitVec.slice r 0 32)))
  let w__2 ← (( do readReg _PMEVCNTR ) : SailM (Vector (BitVec 32) 31) )
  writeReg _PMEVCNTR (vectorUpdate w__2 n r)


def PMOVSR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMOVSR_Type := value_name
  let w__0 ← (( do readReg PMOVSCLR_EL0 ) : SailM (BitVec 64) )
  writeReg PMOVSCLR_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _PMOVSR r


def undefined_PMOVSSET_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_PMOVSSET_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def PMOVSSET_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _PMOVSSET ) : SailM PMOVSSET_Type )
  let w__0 ← (( do readReg PMOVSSET_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def PMOVSSET_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMOVSSET_Type := value_name
  let w__0 ← (( do readReg PMOVSSET_EL0 ) : SailM (BitVec 64) )
  writeReg PMOVSSET_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _PMOVSSET r


def undefined_PMCCNTR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_PMCCNTR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def PMCCNTR_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _PMCCNTR ) : SailM PMCCNTR_Type )
  let w__0 ← (( do readReg PMCCNTR_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 63 0 (BitVec.slice w__0 0 64)) : (BitVec 64))
  (pure (r))


def PMCCNTR_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : PMCCNTR_Type := value_name
  let w__0 ← (( do readReg PMCCNTR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCCNTR_EL0 (Sail.BitVec.updateSubrange w__0 63 0 (BitVec.slice r 0 64))
  writeReg _PMCCNTR r


def Mk_ID_MMFR2_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ID_MMFR2_EL1_Type_HWAccFlg (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _update_ID_MMFR2_EL1_Type_HWAccFlg (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _get_ID_MMFR2_Type_HWAccFlg (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _get_ID_MMFR2_EL1_Type_HvdTLB (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _update_ID_MMFR2_EL1_Type_HvdTLB (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _get_ID_MMFR2_Type_HvdTLB (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _get_ID_MMFR2_EL1_Type_L1HvdBG (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_ID_MMFR2_EL1_Type_L1HvdBG (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_ID_MMFR2_Type_L1HvdBG (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_ID_MMFR2_EL1_Type_L1HvdFG (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_ID_MMFR2_EL1_Type_L1HvdFG (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_ID_MMFR2_Type_L1HvdFG (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_ID_MMFR2_EL1_Type_L1HvdRng (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _update_ID_MMFR2_EL1_Type_L1HvdRng (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_ID_MMFR2_Type_L1HvdRng (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _get_ID_MMFR2_EL1_Type_MemBarr (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _update_ID_MMFR2_EL1_Type_MemBarr (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _get_ID_MMFR2_Type_MemBarr (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _get_ID_MMFR2_EL1_Type_UniTLB (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_ID_MMFR2_EL1_Type_UniTLB (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_ID_MMFR2_Type_UniTLB (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_ID_MMFR2_EL1_Type_WFIStall (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _update_ID_MMFR2_EL1_Type_WFIStall (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _get_ID_MMFR2_Type_WFIStall (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def Mk_ID_MMFR4_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ID_MMFR4_EL1_Type_AC2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_ID_MMFR4_EL1_Type_AC2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_ID_MMFR4_Type_AC2 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_ID_MMFR4_Type_AC2 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_ID_MMFR4_EL1_Type_CCIDX (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _update_ID_MMFR4_EL1_Type_CCIDX (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _update_ID_AA64MMFR2_EL1_Type_CCIDX (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _get_ID_AA64MMFR2_EL1_Type_CCIDX (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _get_ID_MMFR4_Type_CCIDX (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_ID_MMFR4_EL1_Type_EVT (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _update_ID_MMFR4_EL1_Type_EVT (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _update_ID_AA64MMFR2_EL1_Type_EVT (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)


def _update_ID_MMFR4_Type_EVT (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _get_ID_AA64MMFR2_EL1_Type_EVT (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)


def _get_ID_MMFR4_Type_EVT (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _get_ID_MMFR4_EL1_Type_HPDS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_ID_MMFR4_EL1_Type_HPDS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_ID_AA64MMFR1_EL1_Type_HPDS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _update_ID_MMFR4_Type_HPDS (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_ID_AA64MMFR1_EL1_Type_HPDS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _get_ID_MMFR4_Type_HPDS (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_ID_MMFR4_EL1_Type_LSM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _update_ID_MMFR4_EL1_Type_LSM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _update_ID_AA64MMFR2_EL1_Type_LSM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _update_ID_MMFR4_Type_LSM (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _get_ID_AA64MMFR2_EL1_Type_LSM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _get_ID_MMFR4_Type_LSM (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _get_ID_MMFR4_EL1_Type_SpecSEI (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_ID_MMFR4_EL1_Type_SpecSEI (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


end ArmFull.Functions
