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

def undefined_GICR_STATUSR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GICR_SYNCR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GICR_VPENDBASER_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_GICR_VPROPBASER_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_GICR_VSGIPENDR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GICR_VSGIR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GICR_WAKER_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GICV_ABPR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GICV_AEOIR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GICV_AHPPIR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GICV_AIAR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GICV_BPR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GICV_CTLR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GICV_DIR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GICV_EOIR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GICV_HPPIR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GICV_IAR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GICV_PMR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GICV_RPR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GICV_STATUSR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GITS_CBASER_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_GITS_CREADR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_GITS_CTLR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GITS_CWRITER_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_GITS_IIDR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GITS_MPAMIDR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GITS_MPIDR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GITS_PARTIDR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GITS_SGIR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_GITS_STATUSR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_GITS_TYPER_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_ICC_MCTLR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_ICC_MGRPEN1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_ICC_MSRE_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_PMAUTHSTATUS_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_PMCFGR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_PMCGCR0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_PMCIDR0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_PMCIDR1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_PMCIDR2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_PMCIDR3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_PMDEVID_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_PMDEVTYPE_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_PMIIDR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_PMITCTRL_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_PMLAR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_PMLSR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_PMMIR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_PMPCSCTL_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_PMPCSR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_PMPIDR0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_PMPIDR1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_PMPIDR2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_PMPIDR3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_PMPIDR4_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_PMVCIDSR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_PMVIDSR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_AMCFGR_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_AMCFGR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def AMCFGR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AMCFGR ) : SailM AMCFGR_Type )
  let w__0 ← (( do readReg AMCFGR_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def AMCFGR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMCFGR_Type := value_name
  let w__0 ← (( do readReg AMCFGR_EL0 ) : SailM (BitVec 64) )
  writeReg AMCFGR_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _AMCFGR r


def undefined_AMCGCR_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_AMCGCR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def AMCGCR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AMCGCR ) : SailM AMCGCR_Type )
  let w__0 ← (( do readReg AMCGCR_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def AMCGCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMCGCR_Type := value_name
  let w__0 ← (( do readReg AMCGCR_EL0 ) : SailM (BitVec 64) )
  writeReg AMCGCR_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _AMCGCR r


def undefined_AMCNTENCLR0_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_AMCNTENCLR0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def AMCNTENCLR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AMCNTENCLR0 ) : SailM AMCNTENCLR0_Type )
  let w__0 ← (( do readReg AMCNTENCLR0_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def AMCNTENCLR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMCNTENCLR0_Type := value_name
  let w__0 ← (( do readReg AMCNTENCLR0_EL0 ) : SailM (BitVec 64) )
  writeReg AMCNTENCLR0_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _AMCNTENCLR0 r


def undefined_AMCNTENCLR1_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_AMCNTENCLR1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def AMCNTENCLR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AMCNTENCLR1 ) : SailM AMCNTENCLR1_Type )
  let w__0 ← (( do readReg AMCNTENCLR1_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def AMCNTENCLR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMCNTENCLR1_Type := value_name
  let w__0 ← (( do readReg AMCNTENCLR1_EL0 ) : SailM (BitVec 64) )
  writeReg AMCNTENCLR1_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _AMCNTENCLR1 r


def undefined_AMCNTENSET0_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_AMCNTENSET0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def AMCNTENSET0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AMCNTENSET0 ) : SailM AMCNTENSET0_Type )
  let w__0 ← (( do readReg AMCNTENSET0_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def AMCNTENSET0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMCNTENSET0_Type := value_name
  let w__0 ← (( do readReg AMCNTENSET0_EL0 ) : SailM (BitVec 64) )
  writeReg AMCNTENSET0_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _AMCNTENSET0 r


def undefined_AMCNTENSET1_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_AMCNTENSET1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def AMCNTENSET1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AMCNTENSET1 ) : SailM AMCNTENSET1_Type )
  let w__0 ← (( do readReg AMCNTENSET1_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def AMCNTENSET1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMCNTENSET1_Type := value_name
  let w__0 ← (( do readReg AMCNTENSET1_EL0 ) : SailM (BitVec 64) )
  writeReg AMCNTENSET1_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _AMCNTENSET1 r


def undefined_AMCR_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_AMCR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def AMCR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AMCR ) : SailM AMCR_Type )
  let w__0 ← (( do readReg AMCR_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def AMCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMCR_Type := value_name
  let w__0 ← (( do readReg AMCR_EL0 ) : SailM (BitVec 64) )
  writeReg AMCR_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _AMCR r


def undefined_AMUSERENR_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_AMUSERENR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def AMUSERENR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AMUSERENR ) : SailM AMUSERENR_Type )
  let w__0 ← (( do readReg AMUSERENR_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def AMUSERENR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMUSERENR_Type := value_name
  let w__0 ← (( do readReg AMUSERENR_EL0 ) : SailM (BitVec 64) )
  writeReg AMUSERENR_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _AMUSERENR r


def undefined_CCSIDR2_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_CCSIDR2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def CCSIDR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CCSIDR2 ) : SailM CCSIDR2_Type )
  let w__0 ← (( do readReg CCSIDR2_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def CCSIDR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CCSIDR2_Type := value_name
  let w__0 ← (( do readReg CCSIDR2_EL1 ) : SailM (BitVec 64) )
  writeReg CCSIDR2_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _CCSIDR2 r


def undefined_CCSIDR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_CCSIDR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def CCSIDR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CCSIDR ) : SailM CCSIDR_Type )
  let w__0 ← (( do readReg CCSIDR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def CCSIDR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CCSIDR_Type := value_name
  let w__0 ← (( do readReg CCSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg CCSIDR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _CCSIDR r


def undefined_CNTHCTL_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def CNTHCTL_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CNTHCTL ) : SailM CNTHCTL_Type )
  let w__0 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def CNTHCTL_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTHCTL_Type := value_name
  let w__0 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHCTL_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _CNTHCTL r


def undefined_CNTHPS_CTL_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def CNTHPS_CTL_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CNTHPS_CTL ) : SailM CNTHPS_CTL_Type )
  let w__0 ← (( do readReg CNTHPS_CTL_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def CNTHPS_CTL_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTHPS_CTL_Type := value_name
  let w__0 ← (( do readReg CNTHPS_CTL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHPS_CTL_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _CNTHPS_CTL r


def undefined_CNTHVS_CTL_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def CNTHVS_CTL_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CNTHVS_CTL ) : SailM CNTHVS_CTL_Type )
  let w__0 ← (( do readReg CNTHVS_CTL_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def CNTHVS_CTL_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTHVS_CTL_Type := value_name
  let w__0 ← (( do readReg CNTHVS_CTL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHVS_CTL_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _CNTHVS_CTL r


def undefined_CNTHV_CTL_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def CNTHV_CTL_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CNTHV_CTL ) : SailM CNTHV_CTL_Type )
  let w__0 ← (( do readReg CNTHV_CTL_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def CNTHV_CTL_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTHV_CTL_Type := value_name
  let w__0 ← (( do readReg CNTHV_CTL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHV_CTL_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _CNTHV_CTL r


def CNTKCTL_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTKCTL_Type := value_name
  let w__0 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
  writeReg CNTKCTL_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _CNTKCTL r


def undefined_CNTV_CTL_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def CNTV_CTL_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CNTV_CTL ) : SailM CNTV_CTL_Type )
  let w__0 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def CNTV_CTL_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTV_CTL_Type := value_name
  let w__0 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
  writeReg CNTV_CTL_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _CNTV_CTL r


def CPACR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CPACR_Type := value_name
  let w__0 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
  writeReg CPACR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _CPACR r


def undefined_CSSELR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def undefined_CSSELR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def CSSELR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CSSELR_NS ) : SailM CSSELR_Type )
  let w__0 ← (( do readReg CSSELR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def CSSELR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CSSELR_Type := value_name
  let w__0 ← (( do readReg CSSELR_EL1 ) : SailM (BitVec 64) )
  writeReg CSSELR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _CSSELR_NS r


def undefined_CTR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def CTR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CTR ) : SailM CTR_Type )
  let w__0 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def CTR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CTR_Type := value_name
  let w__0 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
  writeReg CTR_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _CTR r


def undefined_DBGAUTHSTATUS_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_DBGAUTHSTATUS_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def DBGAUTHSTATUS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DBGAUTHSTATUS ) : SailM DBGAUTHSTATUS_Type )
  let w__0 ← (( do readReg DBGAUTHSTATUS_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def DBGAUTHSTATUS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGAUTHSTATUS_Type := value_name
  let w__0 ← (( do readReg DBGAUTHSTATUS_EL1 ) : SailM (BitVec 64) )
  writeReg DBGAUTHSTATUS_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _DBGAUTHSTATUS r


def undefined_DBGCLAIMCLR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_DBGCLAIMCLR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def DBGCLAIMCLR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DBGCLAIMCLR ) : SailM DBGCLAIMCLR_Type )
  let w__0 ← (( do readReg DBGCLAIMCLR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def DBGCLAIMCLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGCLAIMCLR_Type := value_name
  let w__0 ← (( do readReg DBGCLAIMCLR_EL1 ) : SailM (BitVec 64) )
  writeReg DBGCLAIMCLR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _DBGCLAIMCLR r


def undefined_DBGCLAIMSET_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_DBGCLAIMSET_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def DBGCLAIMSET_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DBGCLAIMSET ) : SailM DBGCLAIMSET_Type )
  let w__0 ← (( do readReg DBGCLAIMSET_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def DBGCLAIMSET_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGCLAIMSET_Type := value_name
  let w__0 ← (( do readReg DBGCLAIMSET_EL1 ) : SailM (BitVec 64) )
  writeReg DBGCLAIMSET_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _DBGCLAIMSET r


def undefined_MDCCINT_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_DBGDCCINT_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def DBGDCCINT_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DBGDCCINT ) : SailM DBGDCCINT_Type )
  let w__0 ← (( do readReg MDCCINT_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def DBGDCCINT_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGDCCINT_Type := value_name
  let w__0 ← (( do readReg MDCCINT_EL1 ) : SailM (BitVec 64) )
  writeReg MDCCINT_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _DBGDCCINT r


def undefined_MDRAR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_DBGDRAR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def DBGDRAR_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _DBGDRAR ) : SailM DBGDRAR_Type )
  let w__0 ← (( do readReg MDRAR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 63 0 (BitVec.slice w__0 0 64)) : (BitVec 64))
  (pure (r))


def DBGDRAR_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : DBGDRAR_Type := value_name
  let w__0 ← (( do readReg MDRAR_EL1 ) : SailM (BitVec 64) )
  writeReg MDRAR_EL1 (Sail.BitVec.updateSubrange w__0 63 0 (BitVec.slice r 0 64))
  writeReg _DBGDRAR r


def DBGOSDLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGOSDLR_Type := value_name
  let w__0 ← (( do readReg OSDLR_EL1 ) : SailM (BitVec 64) )
  writeReg OSDLR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _DBGOSDLR r


def DBGOSLSR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGOSLSR_Type := value_name
  let w__0 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
  writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _DBGOSLSR r


def DBGPRCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGPRCR_Type := value_name
  let w__0 ← (( do readReg DBGPRCR_EL1 ) : SailM (BitVec 64) )
  writeReg DBGPRCR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _DBGPRCR r


def undefined_DBGVCR32_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_DBGVCR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def DBGVCR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DBGVCR ) : SailM DBGVCR_Type )
  let w__0 ← (( do readReg DBGVCR32_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def DBGVCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGVCR_Type := value_name
  let w__0 ← (( do readReg DBGVCR32_EL2 ) : SailM (BitVec 64) )
  writeReg DBGVCR32_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _DBGVCR r


def DFSR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DFSR_NS ) : SailM DFSR_Type )
  let w__0 ← (( do readReg ESR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


end ArmFull.Functions
