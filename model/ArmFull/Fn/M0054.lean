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

def DISR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DISR ) : SailM DISR_Type )
  let w__0 ← (( do readReg DISR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def DSPSR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DSPSR2 ) : SailM DSPSR2_Type )
  let w__0 ← (( do readReg DSPSR_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 32 32)) : (BitVec 32))
  (pure (r))


def EDECCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : EDECCR_Type := value_name
  let w__0 ← (( do readReg OSECCR_EL1 ) : SailM (BitVec 64) )
  writeReg OSECCR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _EDECCR r


def EDSCR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : EDSCR2_Type := value_name
  let w__0 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__0 63 32 (BitVec.slice r 0 32))
  writeReg _EDSCR2 r


def undefined_ERRIDR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ERRIDR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ERRIDR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERRIDR ) : SailM ERRIDR_Type )
  let w__0 ← (( do readReg ERRIDR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ERRIDR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERRIDR_Type := value_name
  let w__0 ← (( do readReg ERRIDR_EL1 ) : SailM (BitVec 64) )
  writeReg ERRIDR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ERRIDR r


def undefined_ERRSELR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ERRSELR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ERRSELR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERRSELR ) : SailM ERRSELR_Type )
  let w__0 ← (( do readReg ERRSELR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ERRSELR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERRSELR_Type := value_name
  let w__0 ← (( do readReg ERRSELR_EL1 ) : SailM (BitVec 64) )
  writeReg ERRSELR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ERRSELR r


def HCPTR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HCPTR_Type := value_name
  let w__0 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _HCPTR r


def HCR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HCR2_Type := value_name
  let w__0 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__0 63 32 (BitVec.slice r 0 32))
  writeReg _HCR2 r


def HDCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HDCR_Type := value_name
  let w__0 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _HDCR r


def undefined_RMR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_HRMR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def HRMR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HRMR ) : SailM HRMR_Type )
  let w__0 ← (( do readReg RMR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def HRMR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HRMR_Type := value_name
  let w__0 ← (( do readReg RMR_EL2 ) : SailM (BitVec 64) )
  writeReg RMR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _HRMR r


def HSCTLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HSCTLR_Type := value_name
  let w__0 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _HSCTLR r


def undefined_HSTR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_HSTR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def HSTR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HSTR ) : SailM HSTR_Type )
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def HSTR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HSTR_Type := value_name
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  writeReg HSTR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _HSTR r


def undefined_HTCR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def HTCR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HTCR ) : SailM HTCR_Type )
  let w__0 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def HTCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HTCR_Type := value_name
  let w__0 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  writeReg TCR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _HTCR r


def undefined_TRFCR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_HTRFCR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def HTRFCR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HTRFCR ) : SailM HTRFCR_Type )
  let w__0 ← (( do readReg TRFCR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def HTRFCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HTRFCR_Type := value_name
  let w__0 ← (( do readReg TRFCR_EL2 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _HTRFCR r


def HVBAR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HVBAR_Type := value_name
  let w__0 ← (( do readReg VBAR_EL2 ) : SailM (BitVec 64) )
  writeReg VBAR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _HVBAR r


def undefined_ICC_ASGI1R_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICC_ASGI1R_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def ICC_ASGI1R_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _ICC_ASGI1R ) : SailM ICC_ASGI1R_Type )
  let w__0 ← (( do readReg ICC_ASGI1R_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 63 0 (BitVec.slice w__0 0 64)) : (BitVec 64))
  (pure (r))


def ICC_ASGI1R_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : ICC_ASGI1R_Type := value_name
  let w__0 ← (( do readReg ICC_ASGI1R_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_ASGI1R_EL1 (Sail.BitVec.updateSubrange w__0 63 0 (BitVec.slice r 0 64))
  writeReg _ICC_ASGI1R r


def undefined_ICC_BPR0_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICC_BPR0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICC_BPR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_BPR0 ) : SailM ICC_BPR0_Type )
  let w__0 ← (( do readReg ICC_BPR0_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICC_BPR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_BPR0_Type := value_name
  let w__0 ← (( do readReg ICC_BPR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_BPR0_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_BPR0 r


def undefined_ICC_BPR1_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICC_BPR1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICC_BPR1_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_BPR1_NS ) : SailM ICC_BPR1_Type )
  let w__0 ← (( do readReg ICC_BPR1_EL1_NS ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICC_BPR1_S_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_BPR1_S ) : SailM ICC_BPR1_Type )
  let w__0 ← (( do readReg ICC_BPR1_EL1_S ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICC_BPR1_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_BPR1_Type := value_name
  let w__0 ← (( do readReg ICC_BPR1_EL1_NS ) : SailM (BitVec 64) )
  writeReg ICC_BPR1_EL1_NS (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_BPR1_NS r


def ICC_BPR1_S_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_BPR1_Type := value_name
  let w__0 ← (( do readReg ICC_BPR1_EL1_S ) : SailM (BitVec 64) )
  writeReg ICC_BPR1_EL1_S (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_BPR1_S r


def undefined_ICC_CTLR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICC_CTLR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICC_CTLR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_CTLR_NS ) : SailM ICC_CTLR_Type )
  let w__0 ← (( do readReg ICC_CTLR_EL1_NS ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICC_CTLR_S_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_CTLR_S ) : SailM ICC_CTLR_Type )
  let w__0 ← (( do readReg ICC_CTLR_EL1_S ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICC_CTLR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_CTLR_Type := value_name
  let w__0 ← (( do readReg ICC_CTLR_EL1_NS ) : SailM (BitVec 64) )
  writeReg ICC_CTLR_EL1_NS (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_CTLR_NS r


def ICC_CTLR_S_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_CTLR_Type := value_name
  let w__0 ← (( do readReg ICC_CTLR_EL1_S ) : SailM (BitVec 64) )
  writeReg ICC_CTLR_EL1_S (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_CTLR_S r


def undefined_ICC_DIR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICC_DIR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICC_DIR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_DIR ) : SailM ICC_DIR_Type )
  let w__0 ← (( do readReg ICC_DIR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICC_DIR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_DIR_Type := value_name
  let w__0 ← (( do readReg ICC_DIR_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_DIR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_DIR r


def undefined_ICC_EOIR0_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICC_EOIR0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICC_EOIR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_EOIR0 ) : SailM ICC_EOIR0_Type )
  let w__0 ← (( do readReg ICC_EOIR0_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICC_EOIR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_EOIR0_Type := value_name
  let w__0 ← (( do readReg ICC_EOIR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_EOIR0_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_EOIR0 r


def undefined_ICC_EOIR1_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICC_EOIR1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICC_EOIR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_EOIR1 ) : SailM ICC_EOIR1_Type )
  let w__0 ← (( do readReg ICC_EOIR1_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICC_EOIR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_EOIR1_Type := value_name
  let w__0 ← (( do readReg ICC_EOIR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_EOIR1_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_EOIR1 r


def undefined_ICC_HPPIR0_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICC_HPPIR0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICC_HPPIR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_HPPIR0 ) : SailM ICC_HPPIR0_Type )
  let w__0 ← (( do readReg ICC_HPPIR0_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICC_HPPIR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_HPPIR0_Type := value_name
  let w__0 ← (( do readReg ICC_HPPIR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_HPPIR0_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_HPPIR0 r


def undefined_ICC_HPPIR1_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICC_HPPIR1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICC_HPPIR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_HPPIR1 ) : SailM ICC_HPPIR1_Type )
  let w__0 ← (( do readReg ICC_HPPIR1_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICC_HPPIR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_HPPIR1_Type := value_name
  let w__0 ← (( do readReg ICC_HPPIR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_HPPIR1_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_HPPIR1 r


def undefined_ICC_SRE_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICC_HSRE_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICC_HSRE_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_HSRE ) : SailM ICC_HSRE_Type )
  let w__0 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICC_HSRE_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_HSRE_Type := value_name
  let w__0 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_HSRE r


def undefined_ICC_IAR0_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICC_IAR0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICC_IAR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_IAR0 ) : SailM ICC_IAR0_Type )
  let w__0 ← (( do readReg ICC_IAR0_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICC_IAR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_IAR0_Type := value_name
  let w__0 ← (( do readReg ICC_IAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_IAR0_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_IAR0 r


def undefined_ICC_IAR1_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICC_IAR1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICC_IAR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_IAR1 ) : SailM ICC_IAR1_Type )
  let w__0 ← (( do readReg ICC_IAR1_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICC_IAR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_IAR1_Type := value_name
  let w__0 ← (( do readReg ICC_IAR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_IAR1_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_IAR1 r


def undefined_ICC_IGRPEN0_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICC_IGRPEN0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICC_IGRPEN0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_IGRPEN0 ) : SailM ICC_IGRPEN0_Type )
  let w__0 ← (( do readReg ICC_IGRPEN0_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICC_IGRPEN0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_IGRPEN0_Type := value_name
  let w__0 ← (( do readReg ICC_IGRPEN0_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_IGRPEN0_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_IGRPEN0 r


def undefined_ICC_IGRPEN1_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICC_IGRPEN1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICC_IGRPEN1_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_IGRPEN1_NS ) : SailM ICC_IGRPEN1_Type )
  let w__0 ← (( do readReg ICC_IGRPEN1_EL1_NS ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICC_IGRPEN1_S_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_IGRPEN1_S ) : SailM ICC_IGRPEN1_Type )
  let w__0 ← (( do readReg ICC_IGRPEN1_EL1_S ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICC_IGRPEN1_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_IGRPEN1_Type := value_name
  let w__0 ← (( do readReg ICC_IGRPEN1_EL1_NS ) : SailM (BitVec 64) )
  writeReg ICC_IGRPEN1_EL1_NS (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_IGRPEN1_NS r


def ICC_IGRPEN1_S_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_IGRPEN1_Type := value_name
  let w__0 ← (( do readReg ICC_IGRPEN1_EL1_S ) : SailM (BitVec 64) )
  writeReg ICC_IGRPEN1_EL1_S (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_IGRPEN1_S r


def undefined_ICC_PMR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICC_PMR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_PMR ) : SailM ICC_PMR_Type )
  let w__0 ← (( do readReg ICC_PMR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICC_PMR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_PMR_Type := value_name
  let w__0 ← (( do readReg ICC_PMR_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_PMR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_PMR r


def undefined_ICC_RPR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICC_RPR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICC_RPR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_RPR ) : SailM ICC_RPR_Type )
  let w__0 ← (( do readReg ICC_RPR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICC_RPR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_RPR_Type := value_name
  let w__0 ← (( do readReg ICC_RPR_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_RPR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_RPR r


def undefined_ICC_SGI0R_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICC_SGI0R_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def ICC_SGI0R_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _ICC_SGI0R ) : SailM ICC_SGI0R_Type )
  let w__0 ← (( do readReg ICC_SGI0R_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 63 0 (BitVec.slice w__0 0 64)) : (BitVec 64))
  (pure (r))


def ICC_SGI0R_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : ICC_SGI0R_Type := value_name
  let w__0 ← (( do readReg ICC_SGI0R_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_SGI0R_EL1 (Sail.BitVec.updateSubrange w__0 63 0 (BitVec.slice r 0 64))
  writeReg _ICC_SGI0R r


def undefined_ICC_SGI1R_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICC_SGI1R_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def ICC_SGI1R_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _ICC_SGI1R ) : SailM ICC_SGI1R_Type )
  let w__0 ← (( do readReg ICC_SGI1R_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 63 0 (BitVec.slice w__0 0 64)) : (BitVec 64))
  (pure (r))


def ICC_SGI1R_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : ICC_SGI1R_Type := value_name
  let w__0 ← (( do readReg ICC_SGI1R_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_SGI1R_EL1 (Sail.BitVec.updateSubrange w__0 63 0 (BitVec.slice r 0 64))
  writeReg _ICC_SGI1R r


def undefined_ICC_SRE_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICC_SRE_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICC_SRE_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_SRE_NS ) : SailM ICC_SRE_Type )
  let w__0 ← (( do readReg ICC_SRE_EL1_NS ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICC_SRE_S_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_SRE_S ) : SailM ICC_SRE_Type )
  let w__0 ← (( do readReg ICC_SRE_EL1_S ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICC_SRE_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_SRE_Type := value_name
  let w__0 ← (( do readReg ICC_SRE_EL1_NS ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL1_NS (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_SRE_NS r


def ICC_SRE_S_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_SRE_Type := value_name
  let w__0 ← (( do readReg ICC_SRE_EL1_S ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL1_S (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_SRE_S r


def undefined_ICH_EISR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICH_EISR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICH_EISR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICH_EISR ) : SailM ICH_EISR_Type )
  let w__0 ← (( do readReg ICH_EISR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICH_EISR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICH_EISR_Type := value_name
  let w__0 ← (( do readReg ICH_EISR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_EISR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICH_EISR r


def undefined_ICH_ELRSR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICH_ELRSR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICH_ELRSR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICH_ELRSR ) : SailM ICH_ELRSR_Type )
  let w__0 ← (( do readReg ICH_ELRSR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICH_ELRSR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICH_ELRSR_Type := value_name
  let w__0 ← (( do readReg ICH_ELRSR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_ELRSR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICH_ELRSR r


def undefined_ICH_HCR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICH_HCR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def ICH_HCR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICH_HCR ) : SailM ICH_HCR_Type )
  let w__0 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ICH_HCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICH_HCR_Type := value_name
  let w__0 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ICH_HCR r


end ArmFull.Functions
