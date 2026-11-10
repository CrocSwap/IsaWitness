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

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICC_AP1R_S_read (n : Nat) : SailM (BitVec 32) := do
  let w__0 ← (( do readReg _ICC_AP1R_S ) : SailM (Vector (BitVec 32) 4) )
  let r : ICC_AP1R_Type := (GetElem?.getElem! w__0 n)
  let w__1 ← (( do readReg ICC_AP1R_EL1_S ) : SailM (Vector (BitVec 64) 4) )
  let r :=
    ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! w__1 n) 0 32)) : (BitVec 32))
  (pure (r))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICC_AP1R_S_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_AP1R_Type := value_name
  let w__0 ← (( do readReg ICC_AP1R_EL1_S ) : SailM (Vector (BitVec 64) 4) )
  let w__1 ← (( do readReg ICC_AP1R_EL1_S ) : SailM (Vector (BitVec 64) 4) )
  writeReg ICC_AP1R_EL1_S (vectorUpdate w__0 n
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__1 n) 31 0 (BitVec.slice r 0 32)))
  let w__2 ← (( do readReg _ICC_AP1R_S ) : SailM (Vector (BitVec 32) 4) )
  writeReg _ICC_AP1R_S (vectorUpdate w__2 n r)


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICC_AP1R_NS_read (n : Nat) : SailM (BitVec 32) := do
  let w__0 ← (( do readReg _ICC_AP1R_NS ) : SailM (Vector (BitVec 32) 4) )
  let r : ICC_AP1R_Type := (GetElem?.getElem! w__0 n)
  let w__1 ← (( do readReg ICC_AP1R_EL1_NS ) : SailM (Vector (BitVec 64) 4) )
  let r :=
    ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! w__1 n) 0 32)) : (BitVec 32))
  (pure (r))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICC_AP1R_NS_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_AP1R_Type := value_name
  let w__0 ← (( do readReg ICC_AP1R_EL1_NS ) : SailM (Vector (BitVec 64) 4) )
  let w__1 ← (( do readReg ICC_AP1R_EL1_NS ) : SailM (Vector (BitVec 64) 4) )
  writeReg ICC_AP1R_EL1_NS (vectorUpdate w__0 n
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__1 n) 31 0 (BitVec.slice r 0 32)))
  let w__2 ← (( do readReg _ICC_AP1R_NS ) : SailM (Vector (BitVec 32) 4) )
  writeReg _ICC_AP1R_NS (vectorUpdate w__2 n r)


def undefined_ICH_AP1R_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_ICH_AP1R_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICH_AP1R_read (n : Nat) : SailM (BitVec 32) := do
  let w__0 ← (( do readReg _ICH_AP1R ) : SailM (Vector (BitVec 32) 4) )
  let r : ICH_AP1R_Type := (GetElem?.getElem! w__0 n)
  let w__1 ← (( do readReg ICH_AP1R_EL2 ) : SailM (Vector (BitVec 64) 4) )
  let r :=
    ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! w__1 n) 0 32)) : (BitVec 32))
  (pure (r))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICH_AP1R_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICH_AP1R_Type := value_name
  let w__0 ← (( do readReg ICH_AP1R_EL2 ) : SailM (Vector (BitVec 64) 4) )
  let w__1 ← (( do readReg ICH_AP1R_EL2 ) : SailM (Vector (BitVec 64) 4) )
  writeReg ICH_AP1R_EL2 (vectorUpdate w__0 n
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__1 n) 31 0 (BitVec.slice r 0 32)))
  let w__2 ← (( do readReg _ICH_AP1R ) : SailM (Vector (BitVec 32) 4) )
  writeReg _ICH_AP1R (vectorUpdate w__2 n r)


def Mk_ID_MMFR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def AMAIR0_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AMAIR0_NS ) : SailM AMAIR0_Type )
  let w__0 ← (( do readReg AMAIR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def AMAIR0_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMAIR0_Type := value_name
  let w__0 ← (( do readReg AMAIR_EL1 ) : SailM (BitVec 64) )
  writeReg AMAIR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _AMAIR0_NS r


def Mk_MVFR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def HAMAIR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HAMAIR0 ) : SailM HAMAIR0_Type )
  let w__0 ← (( do readReg AMAIR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def HAMAIR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HAMAIR0_Type := value_name
  let w__0 ← (( do readReg AMAIR_EL2 ) : SailM (BitVec 64) )
  writeReg AMAIR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _HAMAIR0 r


def undefined_ICH_AP0R_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_ICH_AP0R_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICH_AP0R_read (n : Nat) : SailM (BitVec 32) := do
  let w__0 ← (( do readReg _ICH_AP0R ) : SailM (Vector (BitVec 32) 4) )
  let r : ICH_AP0R_Type := (GetElem?.getElem! w__0 n)
  let w__1 ← (( do readReg ICH_AP0R_EL2 ) : SailM (Vector (BitVec 64) 4) )
  let r :=
    ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! w__1 n) 0 32)) : (BitVec 32))
  (pure (r))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICH_AP0R_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICH_AP0R_Type := value_name
  let w__0 ← (( do readReg ICH_AP0R_EL2 ) : SailM (Vector (BitVec 64) 4) )
  let w__1 ← (( do readReg ICH_AP0R_EL2 ) : SailM (Vector (BitVec 64) 4) )
  writeReg ICH_AP0R_EL2 (vectorUpdate w__0 n
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__1 n) 31 0 (BitVec.slice r 0 32)))
  let w__2 ← (( do readReg _ICH_AP0R ) : SailM (Vector (BitVec 32) 4) )
  writeReg _ICH_AP0R (vectorUpdate w__2 n r)


def AIDR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AIDR ) : SailM AIDR_Type )
  let w__0 ← (( do readReg AIDR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def Mk_ID_PFR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def HMAIR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HMAIR1_Type := value_name
  let w__0 ← (( do readReg MAIR_EL2 ) : SailM (BitVec 64) )
  writeReg MAIR_EL2 (Sail.BitVec.updateSubrange w__0 63 32 (BitVec.slice r 0 32))
  writeReg _HMAIR1 r


def PMCEID3_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _PMCEID3 ) : SailM PMCEID3_Type )
  let w__0 ← (( do readReg PMCEID1_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 32 32)) : (BitVec 32))
  (pure (r))


def Mk_ID_ISAR4_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def PMCEID2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _PMCEID2 ) : SailM PMCEID2_Type )
  let w__0 ← (( do readReg PMCEID0_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 32 32)) : (BitVec 32))
  (pure (r))


def HSR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HSR ) : SailM HSR_Type )
  let w__0 ← (( do readReg ESR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def undefined_ICH_LR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_ICH_LR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def ICH_LR_read (n : Nat) : SailM (BitVec 32) := do
  let w__0 ← (( do readReg _ICH_LR ) : SailM (Vector (BitVec 32) 16) )
  let r : ICH_LR_Type := (GetElem?.getElem! w__0 n)
  let w__1 ← (( do readReg ICH_LR_EL2 ) : SailM (Vector (BitVec 64) 16) )
  let r :=
    ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! w__1 n) 0 32)) : (BitVec 32))
  (pure (r))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def ICH_LR_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICH_LR_Type := value_name
  let w__0 ← (( do readReg ICH_LR_EL2 ) : SailM (Vector (BitVec 64) 16) )
  let w__1 ← (( do readReg ICH_LR_EL2 ) : SailM (Vector (BitVec 64) 16) )
  writeReg ICH_LR_EL2 (vectorUpdate w__0 n
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__1 n) 31 0 (BitVec.slice r 0 32)))
  let w__2 ← (( do readReg _ICH_LR ) : SailM (Vector (BitVec 32) 16) )
  writeReg _ICH_LR (vectorUpdate w__2 n r)


def HADFSR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HADFSR ) : SailM HADFSR_Type )
  let w__0 ← (( do readReg AFSR0_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def HADFSR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HADFSR_Type := value_name
  let w__0 ← (( do readReg AFSR0_EL2 ) : SailM (BitVec 64) )
  writeReg AFSR0_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _HADFSR r


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def DBGBCR_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGBCR_Type := value_name
  let w__0 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
  let w__1 ← (( do readReg DBGBCR_EL1 ) : SailM (Vector (BitVec 64) 64) )
  writeReg DBGBCR_EL1 (vectorUpdate w__0 n
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__1 n) 31 0 (BitVec.slice r 0 32)))
  let w__2 ← (( do readReg _DBGBCR ) : SailM (Vector (BitVec 32) 16) )
  writeReg _DBGBCR (vectorUpdate w__2 n r)


def Mk_ID_ISAR3_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICC_MGRPEN1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_TLBTR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_TLBTR_Type_nU (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_TLBTR_Type_nU (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def CNTFRQ_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CNTFRQ ) : SailM CNTFRQ_Type )
  let w__0 ← (( do readReg CNTFRQ_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def CNTFRQ_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTFRQ_Type := value_name
  let w__0 ← (( do readReg CNTFRQ_EL0 ) : SailM (BitVec 64) )
  writeReg CNTFRQ_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _CNTFRQ r


def undefined_PMINTENSET_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_PMINTENSET_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def PMINTENSET_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _PMINTENSET ) : SailM PMINTENSET_Type )
  let w__0 ← (( do readReg PMINTENSET_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def PMINTENSET_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMINTENSET_Type := value_name
  let w__0 ← (( do readReg PMINTENSET_EL1 ) : SailM (BitVec 64) )
  writeReg PMINTENSET_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _PMINTENSET r


def Mk_DBGDEVID_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_DBGDEVID_Type_AuxRegs (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _update_DBGDEVID_Type_AuxRegs (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _update_EDDEVID_Type_AuxRegs (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _get_EDDEVID_Type_AuxRegs (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_DBGDEVID_Type_BPAddrMask (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _update_DBGDEVID_Type_BPAddrMask (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_DBGDEVID_Type_CIDMask (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _update_DBGDEVID_Type_CIDMask (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _get_DBGDEVID_Type_VectorCatch (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _update_DBGDEVID_Type_VectorCatch (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _get_DBGDEVID_Type_VirtExtns (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_DBGDEVID_Type_VirtExtns (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_DBGDEVID_Type_WPAddrMask (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_DBGDEVID_Type_WPAddrMask (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def undefined_DBGOSECCR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_DBGOSECCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def DBGOSECCR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DBGOSECCR ) : SailM DBGOSECCR_Type )
  let w__0 ← (( do readReg OSECCR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def DBGOSECCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGOSECCR_Type := value_name
  let w__0 ← (( do readReg OSECCR_EL1 ) : SailM (BitVec 64) )
  writeReg OSECCR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _DBGOSECCR r


def ACTLR2_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ACTLR2_NS ) : SailM ACTLR2_Type )
  let w__0 ← (( do readReg ACTLR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 32 32)) : (BitVec 32))
  (pure (r))


def ACTLR2_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ACTLR2_Type := value_name
  let w__0 ← (( do readReg ACTLR_EL1 ) : SailM (BitVec 64) )
  writeReg ACTLR_EL1 (Sail.BitVec.updateSubrange w__0 63 32 (BitVec.slice r 0 32))
  writeReg _ACTLR2_NS r


def Mk_ID_MMFR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def HAMAIR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HAMAIR1 ) : SailM HAMAIR1_Type )
  let w__0 ← (( do readReg AMAIR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 32 32)) : (BitVec 32))
  (pure (r))


def HAMAIR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HAMAIR1_Type := value_name
  let w__0 ← (( do readReg AMAIR_EL2 ) : SailM (BitVec 64) )
  writeReg AMAIR_EL2 (Sail.BitVec.updateSubrange w__0 63 32 (BitVec.slice r 0 32))
  writeReg _HAMAIR1 r


def HAIFSR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HAIFSR ) : SailM HAIFSR_Type )
  let w__0 ← (( do readReg AFSR1_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def HAIFSR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HAIFSR_Type := value_name
  let w__0 ← (( do readReg AFSR1_EL2 ) : SailM (BitVec 64) )
  writeReg AFSR1_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _HAIFSR r


def Mk_ID_PFR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def ELR_hyp_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ELR_hyp ) : SailM ELR_hyp_Type )
  let w__0 ← (( do readReg ELR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def Mk_MIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICC_AP0R_read (n : Nat) : SailM (BitVec 32) := do
  let w__0 ← (( do readReg _ICC_AP0R ) : SailM (Vector (BitVec 32) 4) )
  let r : ICC_AP0R_Type := (GetElem?.getElem! w__0 n)
  let w__1 ← (( do readReg ICC_AP0R_EL1 ) : SailM (Vector (BitVec 64) 4) )
  let r :=
    ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! w__1 n) 0 32)) : (BitVec 32))
  (pure (r))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def ICC_AP0R_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_AP0R_Type := value_name
  let w__0 ← (( do readReg ICC_AP0R_EL1 ) : SailM (Vector (BitVec 64) 4) )
  let w__1 ← (( do readReg ICC_AP0R_EL1 ) : SailM (Vector (BitVec 64) 4) )
  writeReg ICC_AP0R_EL1 (vectorUpdate w__0 n
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__1 n) 31 0 (BitVec.slice r 0 32)))
  let w__2 ← (( do readReg _ICC_AP0R ) : SailM (Vector (BitVec 32) 4) )
  writeReg _ICC_AP0R (vectorUpdate w__2 n r)


def Mk_DBGDIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_DBGDIDR_Type_SE_imp (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _update_DBGDIDR_Type_SE_imp (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _get_DBGDIDR_Type_Version (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_DBGDIDR_Type_Version (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_DBGDIDR_Type_nSUHD_imp (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _update_DBGDIDR_Type_nSUHD_imp (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def __set_CNTP_CTL_S (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTP_CTL_Type := value_name
  let w__0 ← (( do readReg CNTP_CTL_S ) : SailM (BitVec 32) )
  writeReg CNTP_CTL_S (Sail.BitVec.updateSubrange w__0 1 0 (BitVec.slice r 0 2))
  let w__1 ← (( do readReg CNTP_CTL_S ) : SailM (BitVec 32) )
  writeReg CNTP_CTL_S (Sail.BitVec.updateSubrange w__1 31 3 (BitVec.slice r 3 29))


def TPIDRPRW_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _TPIDRPRW_NS ) : SailM TPIDRPRW_Type )
  let w__0 ← (( do readReg TPIDR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def TPIDRPRW_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TPIDRPRW_Type := value_name
  let w__0 ← (( do readReg TPIDR_EL1 ) : SailM (BitVec 64) )
  writeReg TPIDR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _TPIDRPRW_NS r


def IFAR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _IFAR_NS ) : SailM IFAR_Type )
  let w__0 ← (( do readReg FAR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 32 32)) : (BitVec 32))
  (pure (r))


def undefined_DBGDTRRXint_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_DBGDTRRXint_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def DBGDTRRXint_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DBGDTRRXint ) : SailM DBGDTRRXint_Type )
  let w__0 ← (( do readReg DBGDTRRX_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def Mk_VPIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 31 -/
def PMEVTYPER_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMEVTYPER_Type := value_name
  let w__0 ← (( do readReg PMEVTYPER_EL0 ) : SailM (Vector (BitVec 64) 32) )
  let w__1 ← (( do readReg PMEVTYPER_EL0 ) : SailM (Vector (BitVec 64) 32) )
  writeReg PMEVTYPER_EL0 (vectorUpdate w__0 n
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__1 n) 31 0 (BitVec.slice r 0 32)))
  let w__2 ← (( do readReg _PMEVTYPER ) : SailM (Vector (BitVec 32) 31) )
  writeReg _PMEVTYPER (vectorUpdate w__2 n r)


def HTPIDR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HTPIDR ) : SailM HTPIDR_Type )
  let w__0 ← (( do readReg TPIDR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def HTPIDR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HTPIDR_Type := value_name
  let w__0 ← (( do readReg TPIDR_EL2 ) : SailM (BitVec 64) )
  writeReg TPIDR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _HTPIDR r


def CONTEXTIDR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CONTEXTIDR_Type := value_name
  let w__0 ← (( do readReg CONTEXTIDR_EL1 ) : SailM (BitVec 64) )
  writeReg CONTEXTIDR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _CONTEXTIDR_NS r


def DFAR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DFAR_NS ) : SailM DFAR_Type )
  let w__0 ← (( do readReg FAR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def PMCNTENCLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMCNTENCLR_Type := value_name
  let w__0 ← (( do readReg PMCNTENCLR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCNTENCLR_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _PMCNTENCLR r


def Mk_ID_ISAR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def undefined_DBGDTRTXint_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_DBGDTRTXint_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def DBGDTRTXint_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGDTRTXint_Type := value_name
  let w__0 ← (( do readReg DBGDTRTX_EL0 ) : SailM (BitVec 64) )
  writeReg DBGDTRTX_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _DBGDTRTXint r


def AMAIR1_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AMAIR1_NS ) : SailM AMAIR1_Type )
  let w__0 ← (( do readReg AMAIR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 32 32)) : (BitVec 32))
  (pure (r))


def AMAIR1_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMAIR1_Type := value_name
  let w__0 ← (( do readReg AMAIR_EL1 ) : SailM (BitVec 64) )
  writeReg AMAIR_EL1 (Sail.BitVec.updateSubrange w__0 63 32 (BitVec.slice r 0 32))
  writeReg _AMAIR1_NS r


def undefined_ICH_LRC_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_ICH_LRC_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def ICH_LRC_read (n : Nat) : SailM (BitVec 32) := do
  let w__0 ← (( do readReg _ICH_LRC ) : SailM (Vector (BitVec 32) 16) )
  let r : ICH_LRC_Type := (GetElem?.getElem! w__0 n)
  let w__1 ← (( do readReg ICH_LR_EL2 ) : SailM (Vector (BitVec 64) 16) )
  let r :=
    ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! w__1 n) 32 32)) : (BitVec 32))
  (pure (r))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def ICH_LRC_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICH_LRC_Type := value_name
  let w__0 ← (( do readReg ICH_LR_EL2 ) : SailM (Vector (BitVec 64) 16) )
  let w__1 ← (( do readReg ICH_LR_EL2 ) : SailM (Vector (BitVec 64) 16) )
  writeReg ICH_LR_EL2 (vectorUpdate w__0 n
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__1 n) 63 32 (BitVec.slice r 0 32)))
  let w__2 ← (( do readReg _ICH_LRC ) : SailM (Vector (BitVec 32) 16) )
  writeReg _ICH_LRC (vectorUpdate w__2 n r)


def MAIR1_S_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : MAIR1_Type := value_name
  let w__0 ← (( do readReg NMRR_S ) : SailM (BitVec 32) )
  writeReg NMRR_S (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _MAIR1_S r


def Mk_ID_ISAR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def undefined_AMEVTYPER0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_AMEVTYPER0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 4 -/
def AMEVTYPER0_read (n : Nat) : SailM (BitVec 32) := do
  let w__0 ← (( do readReg _AMEVTYPER0 ) : SailM (Vector (BitVec 32) 4) )
  let r : AMEVTYPER0_Type := (GetElem?.getElem! w__0 n)
  let w__1 ← (( do readReg AMEVTYPER0_EL0 ) : SailM (Vector (BitVec 64) 4) )
  let r :=
    ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! w__1 n) 0 32)) : (BitVec 32))
  (pure (r))


def undefined_AMEVTYPER1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_AMEVTYPER1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def AMEVTYPER1_read (n : Nat) : SailM (BitVec 32) := do
  let w__0 ← (( do readReg _AMEVTYPER1 ) : SailM (Vector (BitVec 32) 16) )
  let r : AMEVTYPER1_Type := (GetElem?.getElem! w__0 n)
  let w__1 ← (( do readReg AMEVTYPER1_EL0 ) : SailM (Vector (BitVec 64) 16) )
  let r :=
    ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (GetElem?.getElem! w__1 n) 0 32)) : (BitVec 32))
  (pure (r))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 16 -/
def AMEVTYPER1_set (n : Nat) (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMEVTYPER1_Type := value_name
  let w__0 ← (( do readReg AMEVTYPER1_EL0 ) : SailM (Vector (BitVec 64) 16) )
  let w__1 ← (( do readReg AMEVTYPER1_EL0 ) : SailM (Vector (BitVec 64) 16) )
  writeReg AMEVTYPER1_EL0 (vectorUpdate w__0 n
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__1 n) 31 0 (BitVec.slice r 0 32)))
  let w__2 ← (( do readReg _AMEVTYPER1 ) : SailM (Vector (BitVec 32) 16) )
  writeReg _AMEVTYPER1 (vectorUpdate w__2 n r)


def ERXFR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXFR2 ) : SailM ERXFR2_Type )
  let w__0 ← (( do readReg ERXFR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 32 32)) : (BitVec 32))
  (pure (r))


def ERXMISC2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXMISC2 ) : SailM ERXMISC2_Type )
  let w__0 ← (( do readReg ERXMISC1_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ERXMISC2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERXMISC2_Type := value_name
  let w__0 ← (( do readReg ERXMISC1_EL1 ) : SailM (BitVec 64) )
  writeReg ERXMISC1_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ERXMISC2 r


def ERXFR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERXFR ) : SailM ERXFR_Type )
  let w__0 ← (( do readReg ERXFR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


end ArmFull.Functions
