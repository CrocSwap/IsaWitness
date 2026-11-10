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

def _update_RMR_Type_RR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_TRFCR_Type_E0TRE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_TRFCR_Type_E1TRE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_VMPIDR_Type_Aff0 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_VMPIDR_Type_Aff1 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 8 x)


def _update_VMPIDR_Type_Aff2 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 16 x)


def _update_VPIDR_Type_Architecture (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_VPIDR_Type_Implementer (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)


def _update_VPIDR_Type_PartNum (v : (BitVec 32)) (x : (BitVec 12)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 4 x)


def _update_VPIDR_Type_Revision (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_VPIDR_Type_Variant (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def undefined_DBGDEVID_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_FPSID_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_ID_DFR0_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_TLBTR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_CLIDR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def CLIDR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CLIDR ) : SailM CLIDR_Type )
  let w__0 ← (( do readReg CLIDR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def CLIDR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CLIDR_Type := value_name
  let w__0 ← (( do readReg CLIDR_EL1 ) : SailM (BitVec 64) )
  writeReg CLIDR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _CLIDR r


def undefined_ID_DFR0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ID_DFR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_DFR0 ) : SailM ID_DFR0_Type )
  let w__0 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ID_DFR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_DFR0_Type := value_name
  let w__0 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ID_DFR0 r


def undefined_ID_ISAR1_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ID_ISAR1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ID_ISAR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_ISAR1 ) : SailM ID_ISAR1_Type )
  let w__0 ← (( do readReg ID_ISAR1_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ID_ISAR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_ISAR1_Type := value_name
  let w__0 ← (( do readReg ID_ISAR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR1_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ID_ISAR1 r


def undefined_ID_ISAR2_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ID_ISAR2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ID_ISAR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_ISAR2 ) : SailM ID_ISAR2_Type )
  let w__0 ← (( do readReg ID_ISAR2_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ID_ISAR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_ISAR2_Type := value_name
  let w__0 ← (( do readReg ID_ISAR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR2_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ID_ISAR2 r


def undefined_ID_ISAR3_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ID_ISAR3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ID_ISAR3_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_ISAR3 ) : SailM ID_ISAR3_Type )
  let w__0 ← (( do readReg ID_ISAR3_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ID_ISAR3_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_ISAR3_Type := value_name
  let w__0 ← (( do readReg ID_ISAR3_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR3_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ID_ISAR3 r


def undefined_ID_ISAR4_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ID_ISAR4_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ID_ISAR4_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_ISAR4 ) : SailM ID_ISAR4_Type )
  let w__0 ← (( do readReg ID_ISAR4_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ID_ISAR4_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_ISAR4_Type := value_name
  let w__0 ← (( do readReg ID_ISAR4_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR4_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ID_ISAR4 r


def undefined_ID_ISAR6_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ID_ISAR6_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ID_ISAR6_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_ISAR6 ) : SailM ID_ISAR6_Type )
  let w__0 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ID_ISAR6_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_ISAR6_Type := value_name
  let w__0 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ID_ISAR6 r


def undefined_ID_MMFR0_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ID_MMFR0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ID_MMFR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_MMFR0 ) : SailM ID_MMFR0_Type )
  let w__0 ← (( do readReg ID_MMFR0_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ID_MMFR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_MMFR0_Type := value_name
  let w__0 ← (( do readReg ID_MMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR0_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ID_MMFR0 r


def undefined_ID_MMFR1_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ID_MMFR1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ID_MMFR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_MMFR1 ) : SailM ID_MMFR1_Type )
  let w__0 ← (( do readReg ID_MMFR1_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ID_MMFR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_MMFR1_Type := value_name
  let w__0 ← (( do readReg ID_MMFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR1_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ID_MMFR1 r


def undefined_ID_MMFR2_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ID_MMFR2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ID_MMFR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_MMFR2 ) : SailM ID_MMFR2_Type )
  let w__0 ← (( do readReg ID_MMFR2_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ID_MMFR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_MMFR2_Type := value_name
  let w__0 ← (( do readReg ID_MMFR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR2_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ID_MMFR2 r


def undefined_ID_MMFR3_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ID_MMFR3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ID_MMFR3_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_MMFR3 ) : SailM ID_MMFR3_Type )
  let w__0 ← (( do readReg ID_MMFR3_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ID_MMFR3_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_MMFR3_Type := value_name
  let w__0 ← (( do readReg ID_MMFR3_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR3_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ID_MMFR3 r


def undefined_ID_MMFR4_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ID_MMFR4_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ID_MMFR4_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_MMFR4 ) : SailM ID_MMFR4_Type )
  let w__0 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ID_MMFR4_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_MMFR4_Type := value_name
  let w__0 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ID_MMFR4 r


def undefined_ID_PFR0_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ID_PFR0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ID_PFR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_PFR0 ) : SailM ID_PFR0_Type )
  let w__0 ← (( do readReg ID_PFR0_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ID_PFR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_PFR0_Type := value_name
  let w__0 ← (( do readReg ID_PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR0_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ID_PFR0 r


def undefined_ID_PFR1_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ID_PFR1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ID_PFR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_PFR1 ) : SailM ID_PFR1_Type )
  let w__0 ← (( do readReg ID_PFR1_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ID_PFR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_PFR1_Type := value_name
  let w__0 ← (( do readReg ID_PFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR1_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ID_PFR1 r


def undefined_MIDR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_MIDR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def MIDR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _MIDR ) : SailM MIDR_Type )
  let w__0 ← (( do readReg MIDR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def MIDR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : MIDR_Type := value_name
  let w__0 ← (( do readReg MIDR_EL1 ) : SailM (BitVec 64) )
  writeReg MIDR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _MIDR r


def undefined_MVFR0_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_MVFR0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def MVFR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _MVFR0 ) : SailM MVFR0_Type )
  let w__0 ← (( do readReg MVFR0_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def MVFR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : MVFR0_Type := value_name
  let w__0 ← (( do readReg MVFR0_EL1 ) : SailM (BitVec 64) )
  writeReg MVFR0_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _MVFR0 r


def undefined_MVFR1_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_MVFR1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def MVFR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _MVFR1 ) : SailM MVFR1_Type )
  let w__0 ← (( do readReg MVFR1_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def MVFR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : MVFR1_Type := value_name
  let w__0 ← (( do readReg MVFR1_EL1 ) : SailM (BitVec 64) )
  writeReg MVFR1_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _MVFR1 r


def Mk_CLIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ID_ISAR6_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_NMRR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PMCEID0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PMCEID1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PMCEID2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PMCEID3_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def undefined_NMRR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def NMRR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _NMRR_NS ) : SailM NMRR_Type )
  let w__0 ← (( do readReg MAIR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 32 32)) : (BitVec 32))
  (pure (r))


def NMRR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : NMRR_Type := value_name
  let w__0 ← (( do readReg MAIR_EL1 ) : SailM (BitVec 64) )
  writeReg MAIR_EL1 (Sail.BitVec.updateSubrange w__0 63 32 (BitVec.slice r 0 32))
  writeReg _NMRR_NS r


def undefined_PMCEID0_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_PMCEID0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def PMCEID0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMCEID0_Type := value_name
  let w__0 ← (( do readReg PMCEID0_EL0 ) : SailM (BitVec 64) )
  writeReg PMCEID0_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _PMCEID0 r


def undefined_PMCEID1_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_PMCEID1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def PMCEID1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMCEID1_Type := value_name
  let w__0 ← (( do readReg PMCEID1_EL0 ) : SailM (BitVec 64) )
  writeReg PMCEID1_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _PMCEID1 r


def undefined_PMCEID2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def PMCEID2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMCEID2_Type := value_name
  let w__0 ← (( do readReg PMCEID0_EL0 ) : SailM (BitVec 64) )
  writeReg PMCEID0_EL0 (Sail.BitVec.updateSubrange w__0 63 32 (BitVec.slice r 0 32))
  writeReg _PMCEID2 r


def undefined_PMCEID3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def PMCEID3_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMCEID3_Type := value_name
  let w__0 ← (( do readReg PMCEID1_EL0 ) : SailM (BitVec 64) )
  writeReg PMCEID1_EL0 (Sail.BitVec.updateSubrange w__0 63 32 (BitVec.slice r 0 32))
  writeReg _PMCEID3 r


def _get_ID_DFR0_EL1_Type_CopDbg (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_ID_DFR0_Type_CopDbg (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_CCSIDR_Type_Associativity (v : (BitVec 32)) (x : (BitVec 21)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 3 x)


def _update_CCSIDR_Type_LineSize (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)


def _update_ID_DFR0_Type_CopDbg (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_ID_DFR0_Type_CopSDbg (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_ID_DFR0_Type_CopTrc (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _update_ID_DFR0_Type_MMapDbg (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _update_ID_DFR0_Type_MMapTrc (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_ID_DFR0_Type_MProfDbg (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _update_ID_DFR0_Type_PerfMon (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _update_ID_DFR0_Type_TraceFilt (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _update_ID_DFR1_Type_MTPMU (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_ID_ISAR0_Type_BitCount (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_ID_ISAR0_Type_BitField (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _update_ID_ISAR0_Type_CmpBranch (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _update_ID_ISAR0_Type_Coproc (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_ID_ISAR0_Type_Debug (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _update_ID_ISAR0_Type_Divide (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _update_ID_ISAR0_Type_Swap (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_ID_ISAR1_Type_Endian (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_ID_ISAR1_Type_Except (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_ID_ISAR1_Type_Except_AR (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _update_ID_ISAR1_Type_Extend (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _update_ID_ISAR1_Type_IfThen (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_ID_ISAR1_Type_Immediate (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _update_ID_ISAR1_Type_Interwork (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _update_ID_ISAR1_Type_Jazelle (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _update_ID_ISAR2_Type_LoadStore (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_ID_ISAR2_Type_MemHint (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_ID_ISAR2_Type_Mult (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _update_ID_ISAR2_Type_MultS (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_ID_ISAR2_Type_MultU (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _update_ID_ISAR2_Type_MultiAccessInt (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _update_ID_ISAR2_Type_PSR_AR (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _update_ID_ISAR2_Type_Reversal (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _update_ID_ISAR3_Type_SIMD (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_ID_ISAR3_Type_SVC (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _update_ID_ISAR3_Type_Saturate (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_ID_ISAR3_Type_SynchPrim (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _update_ID_ISAR3_Type_T32Copy (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _update_ID_ISAR3_Type_T32EE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _update_ID_ISAR3_Type_TabBranch (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_ID_ISAR3_Type_TrueNOP (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _update_ID_ISAR4_Type_Barrier (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_ID_ISAR4_Type_PSR_M (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _update_ID_ISAR4_Type_SMC (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _update_ID_ISAR4_Type_SWP_frac (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


def _update_ID_ISAR4_Type_SynchPrim_frac (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _update_ID_ISAR4_Type_Unpriv (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_ID_ISAR4_Type_WithShifts (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_ID_ISAR4_Type_Writeback (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _update_ID_ISAR5_Type_AES (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _update_ID_ISAR5_Type_CRC32 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_ID_ISAR5_Type_RDM (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _update_ID_ISAR5_Type_SEVL (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_ID_ISAR5_Type_SHA1 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _update_ID_ISAR5_Type_SHA2 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _update_ID_ISAR5_Type_VCMA (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)


end ArmFull.Functions
