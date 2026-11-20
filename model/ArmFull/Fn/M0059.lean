module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork set_option backward.proofsInPublic true @[expose] public section

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

def _get_ID_AA64DFR0_EL1_Type_CTX_CMPs (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)


def _get_ID_AA64DFR0_EL1_Type_PMUVer (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _get_ID_AA64DFR0_EL1_Type_TraceFilt (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)


def _get_ID_AA64DFR0_EL1_Type_TraceVer (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_ID_AA64DFR0_EL1_Type_WRPs (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _get_ID_AA64PFR0_EL1_Type_AdvSIMD (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _get_ID_AA64PFR0_EL1_Type_EL0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_ID_AA64PFR0_EL1_Type_EL1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _get_ID_AA64PFR0_EL1_Type_EL2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _get_ID_AA64PFR0_EL1_Type_EL3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _get_ID_AA64PFR0_EL1_Type_GIC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_ID_AA64PFR0_EL1_Type_MPAM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)


def _get_ID_AA64PFR1_EL1_Type_MPAM_frac (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_ICC_CTLR_EL1_Type_A3V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _update_ICC_CTLR_EL1_Type_ExtRange (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)


def _update_ICC_CTLR_EL1_Type_IDbits (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 11 x)


def _update_ICC_CTLR_EL1_Type_PRIbits (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 8 x)


def _TLBInvalidate (_ : Unit) : Unit :=
  ()


def AArch32_ITAdvance (_ : Unit) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb w__0.IT 2 0)) == 0b000#3) : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with IT := 0b00000000#8 })
  else
    (do
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with IT := (Sail.BitVec.updateSubrange w__3.IT 4 0
          ((Sail.BitVec.extractLsb w__4.IT 4 0) <<< 1)) })


def Mk_HSTR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_HSTR_EL2_Type_T0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_HSTR_EL2_Type_T0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_HSTR_Type_T0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_HSTR_EL2_Type_T1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_HSTR_EL2_Type_T1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_HSTR_Type_T1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_HSTR_EL2_Type_T10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _update_HSTR_EL2_Type_T10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _get_HSTR_Type_T10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _get_HSTR_EL2_Type_T11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)


def _update_HSTR_EL2_Type_T11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _get_HSTR_Type_T11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)


def _get_HSTR_EL2_Type_T12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _update_HSTR_EL2_Type_T12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _get_HSTR_Type_T12 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _get_HSTR_EL2_Type_T13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _update_HSTR_EL2_Type_T13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _get_HSTR_Type_T13 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _get_HSTR_EL2_Type_T15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _update_HSTR_EL2_Type_T15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _get_HSTR_Type_T15 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _get_HSTR_EL2_Type_T2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_HSTR_EL2_Type_T2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_HSTR_Type_T2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_HSTR_EL2_Type_T3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_HSTR_EL2_Type_T3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_HSTR_Type_T3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_HSTR_EL2_Type_T5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _update_HSTR_EL2_Type_T5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _get_HSTR_Type_T5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_HSTR_EL2_Type_T6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _update_HSTR_EL2_Type_T6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _get_HSTR_Type_T6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_HSTR_EL2_Type_T7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _update_HSTR_EL2_Type_T7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _get_HSTR_Type_T7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _get_HSTR_EL2_Type_T8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)


def _update_HSTR_EL2_Type_T8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)


def _get_HSTR_Type_T8 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)


def _get_HSTR_EL2_Type_T9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def _update_HSTR_EL2_Type_T9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


def _get_HSTR_Type_T9 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def Mk_MDSELR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_PMCCNTR_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_PMCCNTR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_PMCCNTR_EL0_Type_CCNT (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)


def _update_PMCCNTR_EL0_Type_CCNT (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)


def _update_PMCCNTR_Type_CCNT (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)


def _update_PMCCNTSVR_EL1_Type_CCNT (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)


def _get_PMCCNTR_Type_CCNT (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)


def _get_PMCCNTSVR_EL1_Type_CCNT (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)


def Mk_PMSICR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_PMSICR_EL1_Type_COUNT (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def _update_PMSICR_EL1_Type_COUNT (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def _get_PMSICR_EL1_Type_ECOUNT (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 63 56)


def _update_PMSICR_EL1_Type_ECOUNT (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 56 x)


def Mk_PMSIRR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_PMSIRR_EL1_Type_INTERVAL (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 31 8)


def _update_PMSIRR_EL1_Type_INTERVAL (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 8 x)


def _get_PMSIRR_EL1_Type_RND (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_PMSIRR_EL1_Type_RND (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def undefined_PMBPTR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_PMBPTR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_PMSDSFR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_PMSDSFR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_PMSDSFR_EL1_Type_S0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_PMSDSFR_EL1_Type_S0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_ERXGSR_EL1_Type_S0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_ERXGSR_EL1_Type_S0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_PMSDSFR_EL1_Type_S1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_PMSDSFR_EL1_Type_S1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_ERXGSR_EL1_Type_S1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_ERXGSR_EL1_Type_S1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_PMSDSFR_EL1_Type_S10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _update_PMSDSFR_EL1_Type_S10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _update_ERXGSR_EL1_Type_S10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _get_ERXGSR_EL1_Type_S10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _get_PMSDSFR_EL1_Type_S11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)


def _update_PMSDSFR_EL1_Type_S11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _update_ERXGSR_EL1_Type_S11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _get_ERXGSR_EL1_Type_S11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)


def _get_PMSDSFR_EL1_Type_S12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _update_PMSDSFR_EL1_Type_S12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _update_ERXGSR_EL1_Type_S12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _get_ERXGSR_EL1_Type_S12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _get_PMSDSFR_EL1_Type_S13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _update_PMSDSFR_EL1_Type_S13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _update_ERXGSR_EL1_Type_S13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _get_ERXGSR_EL1_Type_S13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _get_PMSDSFR_EL1_Type_S14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _update_PMSDSFR_EL1_Type_S14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _update_ERXGSR_EL1_Type_S14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _get_ERXGSR_EL1_Type_S14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _get_PMSDSFR_EL1_Type_S15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _update_PMSDSFR_EL1_Type_S15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _update_ERXGSR_EL1_Type_S15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _get_ERXGSR_EL1_Type_S15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _get_PMSDSFR_EL1_Type_S16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _update_PMSDSFR_EL1_Type_S16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _update_ERXGSR_EL1_Type_S16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _get_ERXGSR_EL1_Type_S16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _get_PMSDSFR_EL1_Type_S17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _update_PMSDSFR_EL1_Type_S17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _update_ERXGSR_EL1_Type_S17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _get_ERXGSR_EL1_Type_S17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _get_PMSDSFR_EL1_Type_S18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)


def _update_PMSDSFR_EL1_Type_S18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)


def _update_ERXGSR_EL1_Type_S18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)


def _get_ERXGSR_EL1_Type_S18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)


def _get_PMSDSFR_EL1_Type_S19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)


def _update_PMSDSFR_EL1_Type_S19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)


def _update_ERXGSR_EL1_Type_S19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)


def _get_ERXGSR_EL1_Type_S19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)


def _get_PMSDSFR_EL1_Type_S2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_PMSDSFR_EL1_Type_S2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_ERXGSR_EL1_Type_S2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_ERXGSR_EL1_Type_S2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_PMSDSFR_EL1_Type_S20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def _update_PMSDSFR_EL1_Type_S20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def _update_ERXGSR_EL1_Type_S20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def _get_ERXGSR_EL1_Type_S20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def _get_PMSDSFR_EL1_Type_S21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


def _update_PMSDSFR_EL1_Type_S21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)


def _update_ERXGSR_EL1_Type_S21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)


def _get_ERXGSR_EL1_Type_S21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


def _get_PMSDSFR_EL1_Type_S22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _update_PMSDSFR_EL1_Type_S22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _update_ERXGSR_EL1_Type_S22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _get_ERXGSR_EL1_Type_S22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _get_PMSDSFR_EL1_Type_S23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)


def _update_PMSDSFR_EL1_Type_S23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)


def _update_ERXGSR_EL1_Type_S23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)


def _get_ERXGSR_EL1_Type_S23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)


def _get_PMSDSFR_EL1_Type_S24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _update_PMSDSFR_EL1_Type_S24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _update_ERXGSR_EL1_Type_S24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _get_ERXGSR_EL1_Type_S24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _get_PMSDSFR_EL1_Type_S25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)


def _update_PMSDSFR_EL1_Type_S25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)


def _update_ERXGSR_EL1_Type_S25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)


def _get_ERXGSR_EL1_Type_S25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)


def _get_PMSDSFR_EL1_Type_S26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)


def _update_PMSDSFR_EL1_Type_S26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)


def _update_ERXGSR_EL1_Type_S26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)


def _get_ERXGSR_EL1_Type_S26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)


def _get_PMSDSFR_EL1_Type_S27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)


def _update_PMSDSFR_EL1_Type_S27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)


def _update_ERXGSR_EL1_Type_S27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)


def _get_ERXGSR_EL1_Type_S27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)


def _get_PMSDSFR_EL1_Type_S28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _update_PMSDSFR_EL1_Type_S28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_ERXGSR_EL1_Type_S28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _get_ERXGSR_EL1_Type_S28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_PMSDSFR_EL1_Type_S29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _update_PMSDSFR_EL1_Type_S29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _update_ERXGSR_EL1_Type_S29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _get_ERXGSR_EL1_Type_S29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _get_PMSDSFR_EL1_Type_S3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_PMSDSFR_EL1_Type_S3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_ERXGSR_EL1_Type_S3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_ERXGSR_EL1_Type_S3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_PMSDSFR_EL1_Type_S30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _update_PMSDSFR_EL1_Type_S30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_ERXGSR_EL1_Type_S30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _get_ERXGSR_EL1_Type_S30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_PMSDSFR_EL1_Type_S31 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _update_PMSDSFR_EL1_Type_S31 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_ERXGSR_EL1_Type_S31 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _get_ERXGSR_EL1_Type_S31 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_PMSDSFR_EL1_Type_S32 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)


def _update_PMSDSFR_EL1_Type_S32 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)


def _update_ERXGSR_EL1_Type_S32 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)


def _get_ERXGSR_EL1_Type_S32 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)


def _get_PMSDSFR_EL1_Type_S33 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)


def _update_PMSDSFR_EL1_Type_S33 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)


def _update_ERXGSR_EL1_Type_S33 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)


end ArmFull.Functions
