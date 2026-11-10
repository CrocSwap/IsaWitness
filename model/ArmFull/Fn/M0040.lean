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

def _get_TCR_EL2_Type_TCMA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _update_TCR_EL2_Type_TCMA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_TCR_EL3_Type_TCMA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _get_TCR_EL3_Type_TCMA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def undefined_TCR_EL3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_TCR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_TCR_EL3_Type_AIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)


def _update_TCR_EL3_Type_AIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)


def _update_ID_AA64MMFR3_EL1_Type_AIE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _update_TCR2_EL1_Type_AIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _update_TCR2_EL2_Type_AIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_ID_AA64MMFR3_EL1_Type_AIE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_TCR2_EL1_Type_AIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _get_TCR2_EL2_Type_AIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _get_TCR_EL3_Type_D128 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 38 38)


def _update_TCR_EL3_Type_D128 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)


def _update_ID_AA64MMFR3_EL1_Type_D128 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)


def _update_PAR_EL1_Type_D128 (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 64 64 x)


def _update_TCR2_EL1_Type_D128 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_TCR2_EL2_Type_D128 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_VTCR_EL2_Type_D128 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)


def _get_ID_AA64MMFR3_EL1_Type_D128 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)


def _get_PAR_EL1_Type_D128 (v : (BitVec 128)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 64 64)


def _get_TCR2_EL1_Type_D128 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_TCR2_EL2_Type_D128 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_VTCR_EL2_Type_D128 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 38 38)


def _get_TCR_EL3_Type_DisCH0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 43 43)


def _update_TCR_EL3_Type_DisCH0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)


def _update_TCR2_EL1_Type_DisCH0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _update_TCR2_EL2_Type_DisCH0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _get_TCR2_EL1_Type_DisCH0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _get_TCR2_EL2_Type_DisCH0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _get_TCR_EL3_Type_HAFT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 42 42)


def _update_TCR_EL3_Type_HAFT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 42 x)


def _update_TCR2_EL1_Type_HAFT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _update_TCR2_EL2_Type_HAFT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _update_VTCR_EL2_Type_HAFT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)


def _get_TCR2_EL1_Type_HAFT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)


def _get_TCR2_EL2_Type_HAFT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)


def _get_VTCR_EL2_Type_HAFT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 44 44)


def _get_TCR_EL3_Type_PIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 35 35)


def _update_TCR_EL3_Type_PIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 35 x)


def _update_TCR2_EL1_Type_PIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_TCR2_EL2_Type_PIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_TCR2_EL1_Type_PIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_TCR2_EL2_Type_PIE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_TCR_EL3_Type_POE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 36 36)


def _update_TCR_EL3_Type_POE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)


def _update_TCR2_EL1_Type_POE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_TCR2_EL2_Type_POE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_TCR2_EL1_Type_POE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_TCR2_EL2_Type_POE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_TCR_EL3_Type_PTTWI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 41 41)


def _update_TCR_EL3_Type_PTTWI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 41 x)


def _update_HCRX_EL2_Type_PTTWI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _update_TCR2_EL1_Type_PTTWI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _update_TCR2_EL2_Type_PTTWI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _get_HCRX_EL2_Type_PTTWI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _get_TCR2_EL1_Type_PTTWI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _get_TCR2_EL2_Type_PTTWI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _get_TCR_EL3_Type_PnCH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 34 34)


def _update_TCR_EL3_Type_PnCH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)


def _update_TCR2_EL1_Type_PnCH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_TCR2_EL2_Type_PnCH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_TCR2_EL1_Type_PnCH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_TCR2_EL2_Type_PnCH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def BranchRawCycleCount (_ : Unit) : SailM Int := do
  let w__0 ← (( do readReg __cycle_count ) : SailM Int )
  let w__1 ← (( do readReg __last_cycle_count ) : SailM Int )
  let diff : Int := (w__0 -i w__1)
  let w__2 ← (( do readReg __cycle_count ) : SailM Int )
  writeReg __last_cycle_count w__2
  (pure (diff))


def FirstBranchAfterProhibited (_ : Unit) : SailM Bool := do
  let w__0 ← (( do readReg __last_branch_valid ) : SailM Bool )
  (pure ((! w__0)))


def BranchMispredict (_ : Unit) : Bool :=
  false


def PC_read (_ : Unit) : SailM (BitVec 64) := do
  readReg _PC


def undefined_BRBIDR0_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_BRBIDR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_BRBIDR0_EL1_Type_FORMAT (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _update_BRBIDR0_EL1_Type_FORMAT (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_BRBIDR0_EL1_Type_NUMREC (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _update_BRBIDR0_EL1_Type_NUMREC (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def undefined_PMSIDR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_PMSIDR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_PMSIDR_EL1_Type_ArchInst (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_PMSIDR_EL1_Type_ArchInst (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_PMSIDR_EL1_Type_CRR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)


def _update_PMSIDR_EL1_Type_CRR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)


def _get_PMSIDR_EL1_Type_CountSize (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_PMSIDR_EL1_Type_CountSize (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_PMSIDR_EL1_Type_ERnd (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _update_PMSIDR_EL1_Type_ERnd (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _get_PMSIDR_EL1_Type_FDS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _update_PMSIDR_EL1_Type_FDS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _update_PMSFCR_EL1_Type_FDS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_PMSFCR_EL1_Type_FDS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _get_PMSIDR_EL1_Type_FE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_PMSIDR_EL1_Type_FE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_PMSFCR_EL1_Type_FE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_PMSFCR_EL1_Type_FE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_PMSIDR_EL1_Type_FL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_PMSIDR_EL1_Type_FL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_PMSFCR_EL1_Type_FL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_PMSFCR_EL1_Type_FL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_PMSIDR_EL1_Type_FT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_PMSIDR_EL1_Type_FT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_PMSFCR_EL1_Type_FT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_PMSFCR_EL1_Type_FT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_PMSIDR_EL1_Type_FnE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _update_PMSIDR_EL1_Type_FnE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_PMSFCR_EL1_Type_FnE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_PMSFCR_EL1_Type_FnE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_PMSIDR_EL1_Type_Format (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _update_PMSIDR_EL1_Type_Format (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _get_PMSIDR_EL1_Type_Interval (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _update_PMSIDR_EL1_Type_Interval (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _get_PMSIDR_EL1_Type_LDS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _update_PMSIDR_EL1_Type_LDS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_PMSIDR_EL1_Type_MaxSize (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _update_PMSIDR_EL1_Type_MaxSize (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _get_PMSIDR_EL1_Type_PBT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _update_PMSIDR_EL1_Type_PBT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def undefined_PMSCR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_PMSCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_PMSCR_EL1_Type_CX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_PMSCR_EL1_Type_CX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_HTRFCR_Type_CX (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_PMSCR_EL2_Type_CX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_TRFCR_EL2_Type_CX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_HTRFCR_Type_CX (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_PMSCR_EL2_Type_CX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_TRFCR_EL2_Type_CX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_PMSCR_EL1_Type_E0SPE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_PMSCR_EL1_Type_E0SPE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_PMSCR_EL1_Type_E1SPE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_PMSCR_EL1_Type_E1SPE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_PMSCR_EL1_Type_PA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _update_PMSCR_EL1_Type_PA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _update_MFAR_EL3_Type_PA (v : (BitVec 64)) (x : (BitVec 56)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange
      (Sail.BitVec.updateSubrange v 55 52
        (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((56 -i 1)))
          (Sail.Int.toNatChecked ((((56 -i 1) -i ((55 -i 52) +i 1)) +i 1))))) 51 48
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((56 -i 1) -i ((55 -i 52) +i 1))))
        (Sail.Int.toNatChecked (((((56 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1)) +i 1)))))
    47 0
    (Sail.BitVec.extractLsb x
      (Sail.Int.toNatChecked ((((56 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1))))
      (Sail.Int.toNatChecked ((((((56 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1)) -i ((47 -i 0) +i 1)) +i 1)))))


def _update_PAR_Type_PA (v : (BitVec 64)) (x : (BitVec 28)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 12 x)


def _update_PFAR_EL1_Type_PA (v : (BitVec 64)) (x : (BitVec 56)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange
      (Sail.BitVec.updateSubrange v 55 52
        (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((56 -i 1)))
          (Sail.Int.toNatChecked ((((56 -i 1) -i ((55 -i 52) +i 1)) +i 1))))) 51 48
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((56 -i 1) -i ((55 -i 52) +i 1))))
        (Sail.Int.toNatChecked (((((56 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1)) +i 1)))))
    47 0
    (Sail.BitVec.extractLsb x
      (Sail.Int.toNatChecked ((((56 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1))))
      (Sail.Int.toNatChecked ((((((56 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1)) -i ((47 -i 0) +i 1)) +i 1)))))


def _update_PFAR_EL2_Type_PA (v : (BitVec 64)) (x : (BitVec 56)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange
      (Sail.BitVec.updateSubrange v 55 52
        (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((56 -i 1)))
          (Sail.Int.toNatChecked ((((56 -i 1) -i ((55 -i 52) +i 1)) +i 1))))) 51 48
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((56 -i 1) -i ((55 -i 52) +i 1))))
        (Sail.Int.toNatChecked (((((56 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1)) +i 1)))))
    47 0
    (Sail.BitVec.extractLsb x
      (Sail.Int.toNatChecked ((((56 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1))))
      (Sail.Int.toNatChecked ((((((56 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1)) -i ((47 -i 0) +i 1)) +i 1)))))


def _update_PMSCR_EL2_Type_PA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_MFAR_EL3_Type_PA (v : (BitVec 64)) : (BitVec 56) :=
  ((Sail.BitVec.extractLsb v 55 52) +++ ((Sail.BitVec.extractLsb v 51 48) +++ (Sail.BitVec.extractLsb
        v 47 0)))


def _get_PAR_Type_PA (v : (BitVec 64)) : (BitVec 28) :=
  (Sail.BitVec.extractLsb v 39 12)


def _get_PFAR_EL1_Type_PA (v : (BitVec 64)) : (BitVec 56) :=
  ((Sail.BitVec.extractLsb v 55 52) +++ ((Sail.BitVec.extractLsb v 51 48) +++ (Sail.BitVec.extractLsb
        v 47 0)))


def _get_PFAR_EL2_Type_PA (v : (BitVec 64)) : (BitVec 56) :=
  ((Sail.BitVec.extractLsb v 55 52) +++ ((Sail.BitVec.extractLsb v 51 48) +++ (Sail.BitVec.extractLsb
        v 47 0)))


def _get_PMSCR_EL2_Type_PA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _get_PMSCR_EL1_Type_PCT (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)


def _update_PMSCR_EL1_Type_PCT (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)


def _update_PMSCR_EL2_Type_PCT (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)


def _get_PMSCR_EL2_Type_PCT (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)


def undefined_PMSCR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_PMSCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_PMSCR_EL2_Type_E0HSPE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_PMSCR_EL2_Type_E0HSPE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_PMSCR_EL2_Type_E2SPE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_PMSCR_EL2_Type_E2SPE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def undefined_PMBLIMITR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_PMBLIMITR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_PMBLIMITR_EL1_Type_FM (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 2 1)


def _update_PMBLIMITR_EL1_Type_FM (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 1 x)


def _get_PMBLIMITR_EL1_Type_LIMIT (v : (BitVec 64)) : (BitVec 52) :=
  (Sail.BitVec.extractLsb v 63 12)


def _update_PMBLIMITR_EL1_Type_LIMIT (v : (BitVec 64)) (x : (BitVec 52)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 12 x)


def _get_PMBLIMITR_EL1_Type_PMFZ (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _update_PMBLIMITR_EL1_Type_PMFZ (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def undefined_PMBSR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_PMBSR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_PMBSR_EL1_Type_AssuredOnly (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 39 39)


def _update_PMBSR_EL1_Type_AssuredOnly (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 39 x)


def _update_PAR_EL1_Type_AssuredOnly (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _update_VTCR_EL2_Type_AssuredOnly (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)


def _get_PAR_EL1_Type_AssuredOnly (v : (BitVec 128)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _get_VTCR_EL2_Type_AssuredOnly (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 34 34)


def _get_PMBSR_EL1_Type_COLL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _update_PMBSR_EL1_Type_COLL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _get_PMBSR_EL1_Type_DL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)


def _update_PMBSR_EL1_Type_DL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)


def _get_PMBSR_EL1_Type_DirtyBit (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)


def _update_PMBSR_EL1_Type_DirtyBit (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)


def _update_PAR_EL1_Type_DirtyBit (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _get_PAR_EL1_Type_DirtyBit (v : (BitVec 128)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _get_PMBSR_EL1_Type_MSS (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _update_PMBSR_EL1_Type_MSS (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _get_PMBSR_EL1_Type_Overlay (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 38 38)


def _update_PMBSR_EL1_Type_Overlay (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)


def _update_PAR_EL1_Type_Overlay (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _get_PAR_EL1_Type_Overlay (v : (BitVec 128)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _get_PMBSR_EL1_Type_S (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _update_PMBSR_EL1_Type_S (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _update_DBGVCR32_EL2_Type_S (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_DBGVCR_Type_S (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_PAR_EL1_Type_S (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


end ArmFull.Functions
