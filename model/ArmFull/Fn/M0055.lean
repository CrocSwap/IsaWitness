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

def undefined_ICH_MISR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICH_MISR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICH_MISR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICH_MISR ) : SailM ICH_MISR_Type )
  let w__0 ← (( do readReg ICH_MISR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICH_MISR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICH_MISR_Type := value_name
  let w__0 ← (( do readReg ICH_MISR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_MISR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICH_MISR r


def undefined_ICH_VMCR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICH_VMCR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICH_VMCR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICH_VMCR ) : SailM ICH_VMCR_Type )
  let w__0 ← (( do readReg ICH_VMCR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICH_VMCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICH_VMCR_Type := value_name
  let w__0 ← (( do readReg ICH_VMCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICH_VMCR r


def undefined_ICH_VTR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICH_VTR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICH_VTR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICH_VTR ) : SailM ICH_VTR_Type )
  let w__0 ← (( do readReg ICH_VTR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICH_VTR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICH_VTR_Type := value_name
  let w__0 ← (( do readReg ICH_VTR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICH_VTR r


def undefined_ICV_BPR0_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICV_BPR0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICV_BPR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_BPR0 ) : SailM ICV_BPR0_Type )
  let w__0 ← (( do readReg ICV_BPR0_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICV_BPR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_BPR0_Type := value_name
  let w__0 ← (( do readReg ICV_BPR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_BPR0_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_BPR0 r


def undefined_ICV_BPR1_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICV_BPR1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICV_BPR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_BPR1 ) : SailM ICV_BPR1_Type )
  let w__0 ← (( do readReg ICV_BPR1_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICV_BPR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_BPR1_Type := value_name
  let w__0 ← (( do readReg ICV_BPR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_BPR1_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_BPR1 r


def undefined_ICV_CTLR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICV_CTLR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICV_CTLR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_CTLR ) : SailM ICV_CTLR_Type )
  let w__0 ← (( do readReg ICV_CTLR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICV_CTLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_CTLR_Type := value_name
  let w__0 ← (( do readReg ICV_CTLR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_CTLR r


def undefined_ICV_DIR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICV_DIR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICV_DIR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_DIR ) : SailM ICV_DIR_Type )
  let w__0 ← (( do readReg ICV_DIR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICV_DIR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_DIR_Type := value_name
  let w__0 ← (( do readReg ICV_DIR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_DIR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_DIR r


def undefined_ICV_EOIR0_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICV_EOIR0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICV_EOIR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_EOIR0 ) : SailM ICV_EOIR0_Type )
  let w__0 ← (( do readReg ICV_EOIR0_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICV_EOIR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_EOIR0_Type := value_name
  let w__0 ← (( do readReg ICV_EOIR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_EOIR0_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_EOIR0 r


def undefined_ICV_EOIR1_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICV_EOIR1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICV_EOIR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_EOIR1 ) : SailM ICV_EOIR1_Type )
  let w__0 ← (( do readReg ICV_EOIR1_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICV_EOIR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_EOIR1_Type := value_name
  let w__0 ← (( do readReg ICV_EOIR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_EOIR1_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_EOIR1 r


def undefined_ICV_HPPIR0_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICV_HPPIR0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICV_HPPIR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_HPPIR0 ) : SailM ICV_HPPIR0_Type )
  let w__0 ← (( do readReg ICV_HPPIR0_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICV_HPPIR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_HPPIR0_Type := value_name
  let w__0 ← (( do readReg ICV_HPPIR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_HPPIR0_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_HPPIR0 r


def undefined_ICV_HPPIR1_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICV_HPPIR1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICV_HPPIR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_HPPIR1 ) : SailM ICV_HPPIR1_Type )
  let w__0 ← (( do readReg ICV_HPPIR1_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICV_HPPIR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_HPPIR1_Type := value_name
  let w__0 ← (( do readReg ICV_HPPIR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_HPPIR1_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_HPPIR1 r


def undefined_ICV_IAR0_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICV_IAR0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICV_IAR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_IAR0 ) : SailM ICV_IAR0_Type )
  let w__0 ← (( do readReg ICV_IAR0_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICV_IAR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_IAR0_Type := value_name
  let w__0 ← (( do readReg ICV_IAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_IAR0_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_IAR0 r


def undefined_ICV_IAR1_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICV_IAR1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICV_IAR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_IAR1 ) : SailM ICV_IAR1_Type )
  let w__0 ← (( do readReg ICV_IAR1_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICV_IAR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_IAR1_Type := value_name
  let w__0 ← (( do readReg ICV_IAR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_IAR1_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_IAR1 r


def undefined_ICV_IGRPEN0_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICV_IGRPEN0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICV_IGRPEN0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_IGRPEN0 ) : SailM ICV_IGRPEN0_Type )
  let w__0 ← (( do readReg ICV_IGRPEN0_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICV_IGRPEN0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_IGRPEN0_Type := value_name
  let w__0 ← (( do readReg ICV_IGRPEN0_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_IGRPEN0_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_IGRPEN0 r


def undefined_ICV_IGRPEN1_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICV_IGRPEN1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICV_IGRPEN1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_IGRPEN1 ) : SailM ICV_IGRPEN1_Type )
  let w__0 ← (( do readReg ICV_IGRPEN1_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICV_IGRPEN1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_IGRPEN1_Type := value_name
  let w__0 ← (( do readReg ICV_IGRPEN1_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_IGRPEN1_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_IGRPEN1 r


def undefined_ICV_PMR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICV_PMR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICV_PMR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_PMR ) : SailM ICV_PMR_Type )
  let w__0 ← (( do readReg ICV_PMR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICV_PMR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_PMR_Type := value_name
  let w__0 ← (( do readReg ICV_PMR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_PMR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_PMR r


def undefined_ICV_RPR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICV_RPR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICV_RPR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_RPR ) : SailM ICV_RPR_Type )
  let w__0 ← (( do readReg ICV_RPR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICV_RPR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_RPR_Type := value_name
  let w__0 ← (( do readReg ICV_RPR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_RPR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_RPR r


def ID_AFR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_AFR0 ) : SailM ID_AFR0_Type )
  let w__0 ← (( do readReg ID_AFR0_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ID_AFR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_AFR0_Type := value_name
  let w__0 ← (( do readReg ID_AFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AFR0_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ID_AFR0 r


def undefined_ID_DFR1_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ID_DFR1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ID_DFR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_DFR1 ) : SailM ID_DFR1_Type )
  let w__0 ← (( do readReg ID_DFR1_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ID_DFR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_DFR1_Type := value_name
  let w__0 ← (( do readReg ID_DFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_DFR1_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ID_DFR1 r


def undefined_ID_ISAR0_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ID_ISAR0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ID_ISAR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_ISAR0 ) : SailM ID_ISAR0_Type )
  let w__0 ← (( do readReg ID_ISAR0_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ID_ISAR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_ISAR0_Type := value_name
  let w__0 ← (( do readReg ID_ISAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR0_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ID_ISAR0 r


def undefined_ID_ISAR5_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ID_ISAR5_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ID_ISAR5_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_ISAR5 ) : SailM ID_ISAR5_Type )
  let w__0 ← (( do readReg ID_ISAR5_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ID_ISAR5_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_ISAR5_Type := value_name
  let w__0 ← (( do readReg ID_ISAR5_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR5_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ID_ISAR5 r


def undefined_ID_MMFR5_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ID_MMFR5_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ID_MMFR5_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_MMFR5 ) : SailM ID_MMFR5_Type )
  let w__0 ← (( do readReg ID_MMFR5_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ID_MMFR5_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_MMFR5_Type := value_name
  let w__0 ← (( do readReg ID_MMFR5_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR5_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ID_MMFR5 r


def undefined_ID_PFR2_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ID_PFR2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ID_PFR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_PFR2 ) : SailM ID_PFR2_Type )
  let w__0 ← (( do readReg ID_PFR2_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ID_PFR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_PFR2_Type := value_name
  let w__0 ← (( do readReg ID_PFR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR2_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ID_PFR2 r


def IFSR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _IFSR_NS ) : SailM IFSR_Type )
  let w__0 ← (( do readReg IFSR32_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def undefined_ISR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ISR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ISR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ISR ) : SailM ISR_Type )
  let w__0 ← (( do readReg ISR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ISR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ISR_Type := value_name
  let w__0 ← (( do readReg ISR_EL1 ) : SailM (BitVec 64) )
  writeReg ISR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ISR r


def undefined_MPIDR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_MPIDR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def MPIDR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _MPIDR ) : SailM MPIDR_Type )
  let w__0 ← (( do readReg MPIDR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def MPIDR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : MPIDR_Type := value_name
  let w__0 ← (( do readReg MPIDR_EL1 ) : SailM (BitVec 64) )
  writeReg MPIDR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _MPIDR r


def undefined_MVFR2_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_MVFR2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def MVFR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _MVFR2 ) : SailM MVFR2_Type )
  let w__0 ← (( do readReg MVFR2_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def MVFR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : MVFR2_Type := value_name
  let w__0 ← (( do readReg MVFR2_EL1 ) : SailM (BitVec 64) )
  writeReg MVFR2_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _MVFR2 r


def Mk_AMCFGR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_AMCGCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_AMCNTENCLR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_AMCNTENCLR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_AMCNTENSET0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_AMCNTENSET1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_AMCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_AMUSERENR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_CCSIDR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_CCSIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_CNTHCTL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_CNTHPS_CTL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_CNTHVS_CTL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_CNTHV_CTL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_CNTV_CTL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_CSSELR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_CTR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_DBGAUTHSTATUS_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_DBGCLAIMCLR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_DBGCLAIMSET_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_DBGDCCINT_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_DBGDRAR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_DBGVCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ERRIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ERRSELR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_HRMR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_HSTR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_HTCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_HTRFCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICC_ASGI1R_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_ICC_BPR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICC_BPR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICC_CTLR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICC_DIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICC_EOIR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICC_EOIR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICC_HPPIR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICC_HPPIR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICC_HSRE_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICC_IAR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICC_IAR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICC_IGRPEN0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICC_IGRPEN1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICC_PMR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


end ArmFull.Functions
