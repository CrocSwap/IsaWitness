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

def Mk_ICC_RPR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICC_SGI0R_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_ICC_SGI1R_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_ICC_SRE_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICH_EISR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICH_ELRSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICH_HCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICH_MISR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICH_VMCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICH_VTR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICV_BPR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICV_BPR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICV_CTLR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICV_DIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICV_EOIR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICV_EOIR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICV_HPPIR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICV_HPPIR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICV_IAR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICV_IAR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICV_IGRPEN0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICV_IGRPEN1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICV_PMR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ICV_RPR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ID_DFR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ID_ISAR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ID_ISAR5_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ID_MMFR5_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ID_PFR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_ISR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_MPIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_MVFR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PAR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_PMCNTEN_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_PMINTEN_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_PMOVS_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def Mk_PMSELR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PMSWINC_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PMUSERENR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_PRRR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_RMR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_TRFCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_TTBCR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_VMPIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def Mk_VTCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def undefined_PAR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def PMCCFILTR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMCCFILTR_Type := value_name
  let w__0 ← (( do readReg PMCCFILTR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCCFILTR_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _PMCCFILTR r


def undefined_PMCNTEN_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def PMCNTEN_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _PMCNTEN ) : SailM PMCNTEN_Type )
  let w__0 ← (( do readReg PMCNTENSET_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 63 0 (BitVec.slice w__0 0 64)) : (BitVec 64))
  (pure (r))


def PMCNTEN_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : PMCNTEN_Type := value_name
  let w__0 ← (( do readReg PMCNTENSET_EL0 ) : SailM (BitVec 64) )
  writeReg PMCNTENSET_EL0 (Sail.BitVec.updateSubrange w__0 63 0 (BitVec.slice r 0 64))
  writeReg _PMCNTEN r


def PMCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMCR_Type := value_name
  let w__0 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _PMCR r


def undefined_PMINTENSET_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_PMINTEN_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def PMINTEN_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _PMINTEN ) : SailM PMINTEN_Type )
  let w__0 ← (( do readReg PMINTENSET_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 63 0 (BitVec.slice w__0 0 64)) : (BitVec 64))
  (pure (r))


def PMINTEN_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : PMINTEN_Type := value_name
  let w__0 ← (( do readReg PMINTENSET_EL1 ) : SailM (BitVec 64) )
  writeReg PMINTENSET_EL1 (Sail.BitVec.updateSubrange w__0 63 0 (BitVec.slice r 0 64))
  writeReg _PMINTEN r


def undefined_PMOVS_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def PMOVS_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _PMOVS ) : SailM PMOVS_Type )
  let w__0 ← (( do readReg PMOVSSET_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 63 0 (BitVec.slice w__0 0 64)) : (BitVec 64))
  (pure (r))


def PMOVS_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : PMOVS_Type := value_name
  let w__0 ← (( do readReg PMOVSSET_EL0 ) : SailM (BitVec 64) )
  writeReg PMOVSSET_EL0 (Sail.BitVec.updateSubrange w__0 63 0 (BitVec.slice r 0 64))
  writeReg _PMOVS r


def undefined_PMSELR_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_PMSELR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def PMSELR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _PMSELR ) : SailM PMSELR_Type )
  let w__0 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def PMSELR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMSELR_Type := value_name
  let w__0 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
  writeReg PMSELR_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _PMSELR r


def undefined_PMSWINC_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_PMSWINC_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def PMSWINC_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _PMSWINC ) : SailM PMSWINC_Type )
  let w__0 ← (( do readReg PMSWINC_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def PMSWINC_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMSWINC_Type := value_name
  let w__0 ← (( do readReg PMSWINC_EL0 ) : SailM (BitVec 64) )
  writeReg PMSWINC_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _PMSWINC r


def undefined_PMUSERENR_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_PMUSERENR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def PMUSERENR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _PMUSERENR ) : SailM PMUSERENR_Type )
  let w__0 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def PMUSERENR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMUSERENR_Type := value_name
  let w__0 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
  writeReg PMUSERENR_EL0 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _PMUSERENR r


def undefined_PRRR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def PRRR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _PRRR_NS ) : SailM PRRR_Type )
  let w__0 ← (( do readReg MAIR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def PRRR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PRRR_Type := value_name
  let w__0 ← (( do readReg MAIR_EL1 ) : SailM (BitVec 64) )
  writeReg MAIR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _PRRR_NS r


def undefined_RMR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_RMR_EL3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_RMR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def SCTLR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : SCTLR_Type := value_name
  let w__0 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _SCTLR_NS r


def SDER32_EL3_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : SDER32_EL3_Type := value_name
  let w__0 ← (( do readReg SDER32_EL2 ) : SailM (BitVec 64) )
  writeReg SDER32_EL2 (Sail.BitVec.updateSubrange w__0 63 0 (BitVec.slice r 0 64))
  writeReg _SDER32_EL3 r


def undefined_TRFCR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_TRFCR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def TRFCR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _TRFCR ) : SailM TRFCR_Type )
  let w__0 ← (( do readReg TRFCR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def TRFCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TRFCR_Type := value_name
  let w__0 ← (( do readReg TRFCR_EL1 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _TRFCR r


def undefined_TTBCR2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def TTBCR2_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _TTBCR2_NS ) : SailM TTBCR2_Type )
  let w__0 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 32 32)) : (BitVec 32))
  (pure (r))


def TTBCR2_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TTBCR2_Type := value_name
  let w__0 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
  writeReg TCR_EL1 (Sail.BitVec.updateSubrange w__0 63 32 (BitVec.slice r 0 32))
  writeReg _TTBCR2_NS r


def TTBCR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TTBCR_Type := value_name
  let w__0 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
  writeReg TCR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _TTBCR_NS r


def VBAR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : VBAR_Type := value_name
  let w__0 ← (( do readReg VBAR_EL1 ) : SailM (BitVec 64) )
  writeReg VBAR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _VBAR_NS r


def VDFSR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : VDFSR_Type := value_name
  let w__0 ← (( do readReg VSESR_EL2 ) : SailM (BitVec 64) )
  writeReg VSESR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _VDFSR r


def VDISR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _VDISR ) : SailM VDISR_Type )
  let w__0 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def undefined_VMPIDR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_VMPIDR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def VMPIDR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _VMPIDR ) : SailM VMPIDR_Type )
  let w__0 ← (( do readReg VMPIDR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def VMPIDR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : VMPIDR_Type := value_name
  let w__0 ← (( do readReg VMPIDR_EL2 ) : SailM (BitVec 64) )
  writeReg VMPIDR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _VMPIDR r


def undefined_VPIDR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def undefined_VPIDR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def VPIDR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _VPIDR ) : SailM VPIDR_Type )
  let w__0 ← (( do readReg VPIDR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def VPIDR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : VPIDR_Type := value_name
  let w__0 ← (( do readReg VPIDR_EL2 ) : SailM (BitVec 64) )
  writeReg VPIDR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _VPIDR r


def undefined_VTCR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def VTCR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _VTCR ) : SailM VTCR_Type )
  let w__0 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def VTCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : VTCR_Type := value_name
  let w__0 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  writeReg VTCR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _VTCR r


def _update_DBGCLAIMCLR_Type_CLAIM (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_DBGCLAIMSET_Type_CLAIM (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_DBGDCCINT_Type_RX (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_DBGDCCINT_Type_TX (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _update_HRMR_Type_RR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_HSTR_Type_T0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_HSTR_Type_T1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_HSTR_Type_T10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _update_HSTR_Type_T11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _update_HSTR_Type_T12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _update_HSTR_Type_T13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _update_HSTR_Type_T15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _update_HSTR_Type_T2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_HSTR_Type_T3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_HSTR_Type_T5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_HSTR_Type_T6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_HSTR_Type_T7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _update_HSTR_Type_T8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)


def _update_HSTR_Type_T9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


def _update_HTRFCR_Type_E0HTRE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_HTRFCR_Type_E2TRE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_ICC_HSRE_Type_DFB (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_ICC_HSRE_Type_DIB (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_ICC_HSRE_Type_SRE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_ICC_IGRPEN0_Type_Enable (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_ICC_IGRPEN1_Type_Enable (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_ICC_SRE_Type_DFB (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_ICC_SRE_Type_DIB (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_ICC_SRE_Type_SRE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_ICH_EISR_Type_Status0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_ICH_EISR_Type_Status1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_ICH_EISR_Type_Status10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _update_ICH_EISR_Type_Status11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _update_ICH_EISR_Type_Status12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _update_ICH_EISR_Type_Status13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _update_ICH_EISR_Type_Status14 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _update_ICH_EISR_Type_Status15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _update_ICH_EISR_Type_Status2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_ICH_EISR_Type_Status3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_ICH_EISR_Type_Status4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _update_ICH_EISR_Type_Status5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_ICH_EISR_Type_Status6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_ICH_EISR_Type_Status7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _update_ICH_EISR_Type_Status8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)


def _update_ICH_EISR_Type_Status9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


def _update_ICH_HCR_Type_EOIcount (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 27 x)


def _update_ICH_HCR_Type_En (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_ICH_HCR_Type_LRENPIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_ICH_HCR_Type_NPIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_ICH_HCR_Type_TALL0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _update_ICH_HCR_Type_TALL1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _update_ICH_HCR_Type_TDIR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _update_ICH_HCR_Type_TSEI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _update_ICH_HCR_Type_UIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_ICH_HCR_Type_VGrp0DIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_ICH_HCR_Type_VGrp0EIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _update_ICH_HCR_Type_VGrp1DIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _update_ICH_HCR_Type_VGrp1EIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_ICH_HCR_Type_vSGIEOICount (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)


def _update_ICH_MISR_Type_EOI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_ICH_MISR_Type_LRENP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_ICH_MISR_Type_NP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_ICH_MISR_Type_VGrp0D (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_ICH_MISR_Type_VGrp0E (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _update_ICH_MISR_Type_VGrp1D (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _update_ICH_MISR_Type_VGrp1E (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_ICV_IGRPEN0_Type_Enable (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_ICV_IGRPEN1_Type_Enable (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


end ArmFull.Functions
