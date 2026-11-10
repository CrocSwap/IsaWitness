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

def _update_SPSR_fiq_Type_V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_SPSR_hyp_Type_V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_SPSR_irq_Type_V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_SPSR_mon_Type_V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_SPSR_svc_Type_V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_SPSR_und_Type_V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _get_DSPSR_EL0_Type_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_DSPSR_Type_V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_FPSCR_Type_V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_GICR_INVALLR_Type_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)


def _get_GICR_INVLPIR_Type_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)


def _get_SCTLR_Type_V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _get_SPSR_EL1_Type_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_SPSR_EL2_Type_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_SPSR_EL3_Type_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_SPSR_abt_Type_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_SPSR_fiq_Type_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_SPSR_hyp_Type_V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_SPSR_irq_Type_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_SPSR_mon_Type_V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_SPSR_svc_Type_V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_SPSR_und_Type_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_FPSR_Type_Z (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _update_FPSR_Type_Z (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_DSPSR_EL0_Type_Z (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_DSPSR_Type_Z (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_FPSCR_Type_Z (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_GICR_VPROPBASER_Type_Z (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)


def _update_SPSR_EL1_Type_Z (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_SPSR_EL2_Type_Z (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_SPSR_EL3_Type_Z (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_SPSR_abt_Type_Z (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_SPSR_fiq_Type_Z (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_SPSR_hyp_Type_Z (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_SPSR_irq_Type_Z (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_SPSR_mon_Type_Z (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_SPSR_svc_Type_Z (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_SPSR_und_Type_Z (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _get_DSPSR_EL0_Type_Z (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_DSPSR_Type_Z (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_FPSCR_Type_Z (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_GICR_VPROPBASER_Type_Z (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 52 52)


def _get_SPSR_EL1_Type_Z (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_SPSR_EL2_Type_Z (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_SPSR_EL3_Type_Z (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_SPSR_abt_Type_Z (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_SPSR_fiq_Type_Z (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_SPSR_hyp_Type_Z (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_SPSR_irq_Type_Z (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_SPSR_mon_Type_Z (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_SPSR_svc_Type_Z (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_SPSR_und_Type_Z (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def undefined_ICC_PMR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_ICC_PMR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ICC_PMR_EL1_Type_Priority (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _update_ICC_PMR_EL1_Type_Priority (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_GICC_PMR_Type_Priority (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_GICC_RPR_Type_Priority (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_GICV_PMR_Type_Priority (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_GICV_RPR_Type_Priority (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_ICC_PMR_Type_Priority (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_ICC_RPR_EL1_Type_Priority (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_ICC_RPR_Type_Priority (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_ICH_LRC_Type_Priority (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 16 x)


def _update_ICH_LR_EL2_Type_Priority (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)


def _update_ICV_PMR_EL1_Type_Priority (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_ICV_PMR_Type_Priority (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_ICV_RPR_EL1_Type_Priority (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_ICV_RPR_Type_Priority (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_SMPRI_EL1_Type_Priority (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_GICC_PMR_Type_Priority (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_GICC_RPR_Type_Priority (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_GICV_PMR_Type_Priority (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_GICV_RPR_Type_Priority (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_ICC_PMR_Type_Priority (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_ICC_RPR_EL1_Type_Priority (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_ICC_RPR_Type_Priority (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_ICH_LRC_Type_Priority (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)


def _get_ICH_LR_EL2_Type_Priority (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)


def _get_ICV_PMR_EL1_Type_Priority (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_ICV_PMR_Type_Priority (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_ICV_RPR_EL1_Type_Priority (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_ICV_RPR_Type_Priority (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_SMPRI_EL1_Type_Priority (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def undefined_TMState (ℓ : ChoiceLabel) (_ : Unit) : SailM TMState := do
  let w__0 ← (( do (undefined_int_at (ℓ.child 0) ()) ) : SailM Int )
  let w__1 ← (( do (undefined_int_at (ℓ.child 1) ()) ) : SailM Int )
  let w__2 ← (( do (undefined_bitvector_at (ℓ.child 2) 64) ) : SailM (BitVec 64) )
  let w__3 ← (( do (undefined_bitvector_at (ℓ.child 3) 64) ) : SailM (BitVec 64) )
  let w__4 ← (( do (undefined_vector 31 w__3) ) : SailM (Vector (BitVec 64) 31) )
  let w__5 ← (( do (undefined_bitvector_at (ℓ.child 4) 2048) ) : SailM (BitVec 2048) )
  let w__6 ← (( do (undefined_vector 32 w__5) ) : SailM (Vector (BitVec 2048) 32) )
  let w__7 ← (( do (undefined_bitvector_at (ℓ.child 5) 256) ) : SailM (BitVec 256) )
  let w__8 ← (( do (undefined_vector 16 w__7) ) : SailM (Vector (BitVec 256) 16) )
  let w__9 ← (( do (undefined_bitvector_at (ℓ.child 6) 256) ) : SailM (BitVec 256) )
  let w__10 ← (( do (undefined_bitvector_at (ℓ.child 7) 64) ) : SailM (BitVec 64) )
  let w__11 ← (( do (undefined_bitvector_at (ℓ.child 8) 64) ) : SailM (BitVec 64) )
  let w__12 ← (( do (undefined_bitvector_at (ℓ.child 9) 64) ) : SailM (BitVec 64) )
  let w__13 ← (( do (undefined_bitvector_at (ℓ.child 10) 64) ) : SailM (BitVec 64) )
  let w__14 ← (( do (undefined_bitvector_at (ℓ.child 11) 64) ) : SailM (BitVec 64) )
  let w__15 ← (( do (undefined_bitvector_at (ℓ.child 12) 4) ) : SailM (BitVec 4) )
  let w__16 ← (( do (undefined_bitvector_at (ℓ.child 13) 1) ) : SailM (BitVec 1) )
  let w__17 ← (( do (undefined_bitvector_at (ℓ.child 14) 1) ) : SailM (BitVec 1) )
  let w__18 ← (( do (undefined_bitvector_at (ℓ.child 15) 1) ) : SailM (BitVec 1) )
  let w__19 ← (( do (undefined_bitvector_at (ℓ.child 16) 1) ) : SailM (BitVec 1) )
  (pure ({ depth := w__0
           Rt := w__1
           nPC := w__2
           X := w__4
           Z := w__6
           P := w__8
           FFR := w__9
           SP := w__10
           FPCR := w__11
           FPSR := w__12
           ICC_PMR_EL1 := w__13
           GCSPR_ELx := w__14
           nzcv := w__15
           D := w__16
           A := w__17
           I := w__18
           F := w__19 }))


def undefined_TMFailure (ℓ : ChoiceLabel) (_ : Unit) : SailM TMFailure := do
  (internal_pick_at (ℓ.child 0)
    [TMFailure_CNCL, TMFailure_DBG, TMFailure_ERR, TMFailure_NEST, TMFailure_SIZE, TMFailure_MEM, TMFailure_TRIVIAL, TMFailure_IMP])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 7 -/
def TMFailure_of_num (arg_ : Nat) : TMFailure :=
  match arg_ with
  | 0 => TMFailure_CNCL
  | 1 => TMFailure_DBG
  | 2 => TMFailure_ERR
  | 3 => TMFailure_NEST
  | 4 => TMFailure_SIZE
  | 5 => TMFailure_MEM
  | 6 => TMFailure_TRIVIAL
  | _ => TMFailure_IMP


def num_of_TMFailure (arg_ : TMFailure) : Int :=
  match arg_ with
  | .TMFailure_CNCL => 0
  | .TMFailure_DBG => 1
  | .TMFailure_ERR => 2
  | .TMFailure_NEST => 3
  | .TMFailure_SIZE => 4
  | .TMFailure_MEM => 5
  | .TMFailure_TRIVIAL => 6
  | .TMFailure_IMP => 7


def undefined_PGSe (ℓ : ChoiceLabel) (_ : Unit) : SailM PGSe := do
  (internal_pick_at (ℓ.child 0) [PGS_4KB, PGS_16KB, PGS_64KB])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def PGSe_of_num (arg_ : Nat) : PGSe :=
  match arg_ with
  | 0 => PGS_4KB
  | 1 => PGS_16KB
  | _ => PGS_64KB


def num_of_PGSe (arg_ : PGSe) : Int :=
  match arg_ with
  | .PGS_4KB => 0
  | .PGS_16KB => 1
  | .PGS_64KB => 2


def GPT_NoAccess : (BitVec 4) := 0b0000#4


def GPT_Table : (BitVec 4) := 0b0011#4


def GPT_Block : (BitVec 4) := 0b0001#4


def GPT_Contig : (BitVec 4) := 0b0001#4


def GPT_Secure : (BitVec 4) := 0b1000#4


def GPT_NonSecure : (BitVec 4) := 0b1001#4


def GPT_Root : (BitVec 4) := 0b1010#4


def GPT_Realm : (BitVec 4) := 0b1011#4


def GPT_Any : (BitVec 4) := 0b1111#4


def GPTRange_4KB : Nat := 12


def GPTRange_16KB : Nat := 14


def GPTRange_64KB : Nat := 16


def GPTRange_2MB : Nat := 21


def GPTRange_32MB : Nat := 25


def GPTRange_512MB : Nat := 29


def GPTRange_1GB : Nat := 30


def GPTRange_16GB : Nat := 34


def GPTRange_64GB : Nat := 36


def GPTRange_512GB : Nat := 39


def undefined_GPTTable (ℓ : ChoiceLabel) (_ : Unit) : SailM GPTTable := do
  let w__0 ← (( do (undefined_bitvector_at (ℓ.child 0) 56) ) : SailM (BitVec 56) )
  (pure ({ address := w__0 }))


def undefined_GPTEntry (ℓ : ChoiceLabel) (_ : Unit) : SailM GPTEntry := do
  let w__0 ← (( do (undefined_bitvector_at (ℓ.child 0) 4) ) : SailM (BitVec 4) )
  let w__1 ← (( do (undefined_int_at (ℓ.child 1) ()) ) : SailM Int )
  let w__2 ← (( do (undefined_int_at (ℓ.child 2) ()) ) : SailM Int )
  let w__3 ← (( do (undefined_int_at (ℓ.child 3) ()) ) : SailM Int )
  let w__4 ← (( do (undefined_bitvector_at (ℓ.child 4) 56) ) : SailM (BitVec 56) )
  (pure ({ gpi := w__0
           size := w__1
           contig_size := w__2
           level := w__3
           pa := w__4 }))


def SPEMaxAddrs : Nat := 32


def SPEMaxCounters : Nat := 32


def SPEMaxRecordSize : Nat := 64


def undefined_TimeStamp (ℓ : ChoiceLabel) (_ : Unit) : SailM TimeStamp := do
  (internal_pick_at (ℓ.child 0)
    [TimeStamp_None, TimeStamp_CoreSight, TimeStamp_Physical, TimeStamp_OffsetPhysical, TimeStamp_Virtual])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def TimeStamp_of_num (arg_ : Nat) : TimeStamp :=
  match arg_ with
  | 0 => TimeStamp_None
  | 1 => TimeStamp_CoreSight
  | 2 => TimeStamp_Physical
  | 3 => TimeStamp_OffsetPhysical
  | _ => TimeStamp_Virtual


def num_of_TimeStamp (arg_ : TimeStamp) : Int :=
  match arg_ with
  | .TimeStamp_None => 0
  | .TimeStamp_CoreSight => 1
  | .TimeStamp_Physical => 2
  | .TimeStamp_OffsetPhysical => 3
  | .TimeStamp_Virtual => 4


def undefined_OpType (ℓ : ChoiceLabel) (_ : Unit) : SailM OpType := do
  (internal_pick_at (ℓ.child 0)
    [OpType_Load, OpType_Store, OpType_LoadAtomic, OpType_Branch, OpType_Other])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def OpType_of_num (arg_ : Nat) : OpType :=
  match arg_ with
  | 0 => OpType_Load
  | 1 => OpType_Store
  | 2 => OpType_LoadAtomic
  | 3 => OpType_Branch
  | _ => OpType_Other


def num_of_OpType (arg_ : OpType) : Int :=
  match arg_ with
  | .OpType_Load => 0
  | .OpType_Store => 1
  | .OpType_LoadAtomic => 2
  | .OpType_Branch => 3
  | .OpType_Other => 4


def SPEAddrPosPCVirtual : Nat := 0


def SPEAddrPosBranchTarget : Nat := 1


def SPEAddrPosDataVirtual : Nat := 2


def SPEAddrPosDataPhysical : Nat := 3


def SPEAddrPosPrevBranchTarget : Nat := 4


def SPECounterPosTotalLatency : Nat := 0


def SPECounterPosIssueLatency : Nat := 1


def SPECounterPosTranslationLatency : Nat := 2


def undefined_CountOp (ℓ : ChoiceLabel) (_ : Unit) : SailM CountOp := do
  (internal_pick_at (ℓ.child 0) [CountOp_CLZ, CountOp_CLS, CountOp_CNT])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def CountOp_of_num (arg_ : Nat) : CountOp :=
  match arg_ with
  | 0 => CountOp_CLZ
  | 1 => CountOp_CLS
  | _ => CountOp_CNT


def num_of_CountOp (arg_ : CountOp) : Int :=
  match arg_ with
  | .CountOp_CLZ => 0
  | .CountOp_CLS => 1
  | .CountOp_CNT => 2


def undefined_ExtendType (ℓ : ChoiceLabel) (_ : Unit) : SailM ExtendType := do
  (internal_pick_at (ℓ.child 0)
    [ExtendType_SXTB, ExtendType_SXTH, ExtendType_SXTW, ExtendType_SXTX, ExtendType_UXTB, ExtendType_UXTH, ExtendType_UXTW, ExtendType_UXTX])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 7 -/
def ExtendType_of_num (arg_ : Nat) : ExtendType :=
  match arg_ with
  | 0 => ExtendType_SXTB
  | 1 => ExtendType_SXTH
  | 2 => ExtendType_SXTW
  | 3 => ExtendType_SXTX
  | 4 => ExtendType_UXTB
  | 5 => ExtendType_UXTH
  | 6 => ExtendType_UXTW
  | _ => ExtendType_UXTX


def num_of_ExtendType (arg_ : ExtendType) : Int :=
  match arg_ with
  | .ExtendType_SXTB => 0
  | .ExtendType_SXTH => 1
  | .ExtendType_SXTW => 2
  | .ExtendType_SXTX => 3
  | .ExtendType_UXTB => 4
  | .ExtendType_UXTH => 5
  | .ExtendType_UXTW => 6
  | .ExtendType_UXTX => 7


def undefined_FPMaxMinOp (ℓ : ChoiceLabel) (_ : Unit) : SailM FPMaxMinOp := do
  (internal_pick_at (ℓ.child 0)
    [FPMaxMinOp_MAX, FPMaxMinOp_MIN, FPMaxMinOp_MAXNUM, FPMaxMinOp_MINNUM])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def FPMaxMinOp_of_num (arg_ : Nat) : FPMaxMinOp :=
  match arg_ with
  | 0 => FPMaxMinOp_MAX
  | 1 => FPMaxMinOp_MIN
  | 2 => FPMaxMinOp_MAXNUM
  | _ => FPMaxMinOp_MINNUM


def num_of_FPMaxMinOp (arg_ : FPMaxMinOp) : Int :=
  match arg_ with
  | .FPMaxMinOp_MAX => 0
  | .FPMaxMinOp_MIN => 1
  | .FPMaxMinOp_MAXNUM => 2
  | .FPMaxMinOp_MINNUM => 3


def undefined_FPUnaryOp (ℓ : ChoiceLabel) (_ : Unit) : SailM FPUnaryOp := do
  (internal_pick_at (ℓ.child 0) [FPUnaryOp_ABS, FPUnaryOp_MOV, FPUnaryOp_NEG, FPUnaryOp_SQRT])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def FPUnaryOp_of_num (arg_ : Nat) : FPUnaryOp :=
  match arg_ with
  | 0 => FPUnaryOp_ABS
  | 1 => FPUnaryOp_MOV
  | 2 => FPUnaryOp_NEG
  | _ => FPUnaryOp_SQRT


def num_of_FPUnaryOp (arg_ : FPUnaryOp) : Int :=
  match arg_ with
  | .FPUnaryOp_ABS => 0
  | .FPUnaryOp_MOV => 1
  | .FPUnaryOp_NEG => 2
  | .FPUnaryOp_SQRT => 3


def undefined_FPConvOp (ℓ : ChoiceLabel) (_ : Unit) : SailM FPConvOp := do
  (internal_pick_at (ℓ.child 0)
    [FPConvOp_CVT_FtoI, FPConvOp_CVT_ItoF, FPConvOp_MOV_FtoI, FPConvOp_MOV_ItoF, FPConvOp_CVT_FtoI_JS])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def FPConvOp_of_num (arg_ : Nat) : FPConvOp :=
  match arg_ with
  | 0 => FPConvOp_CVT_FtoI
  | 1 => FPConvOp_CVT_ItoF
  | 2 => FPConvOp_MOV_FtoI
  | 3 => FPConvOp_MOV_ItoF
  | _ => FPConvOp_CVT_FtoI_JS


def num_of_FPConvOp (arg_ : FPConvOp) : Int :=
  match arg_ with
  | .FPConvOp_CVT_FtoI => 0
  | .FPConvOp_CVT_ItoF => 1
  | .FPConvOp_MOV_FtoI => 2
  | .FPConvOp_MOV_ItoF => 3
  | .FPConvOp_CVT_FtoI_JS => 4


def undefined_MoveWideOp (ℓ : ChoiceLabel) (_ : Unit) : SailM MoveWideOp := do
  (internal_pick_at (ℓ.child 0) [MoveWideOp_N, MoveWideOp_Z, MoveWideOp_K])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def MoveWideOp_of_num (arg_ : Nat) : MoveWideOp :=
  match arg_ with
  | 0 => MoveWideOp_N
  | 1 => MoveWideOp_Z
  | _ => MoveWideOp_K


def num_of_MoveWideOp (arg_ : MoveWideOp) : Int :=
  match arg_ with
  | .MoveWideOp_N => 0
  | .MoveWideOp_Z => 1
  | .MoveWideOp_K => 2


def undefined_ShiftType (ℓ : ChoiceLabel) (_ : Unit) : SailM ShiftType := do
  (internal_pick_at (ℓ.child 0) [ShiftType_LSL, ShiftType_LSR, ShiftType_ASR, ShiftType_ROR])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def ShiftType_of_num (arg_ : Nat) : ShiftType :=
  match arg_ with
  | 0 => ShiftType_LSL
  | 1 => ShiftType_LSR
  | 2 => ShiftType_ASR
  | _ => ShiftType_ROR


def num_of_ShiftType (arg_ : ShiftType) : Int :=
  match arg_ with
  | .ShiftType_LSL => 0
  | .ShiftType_LSR => 1
  | .ShiftType_ASR => 2
  | .ShiftType_ROR => 3


def undefined_LogicalOp (ℓ : ChoiceLabel) (_ : Unit) : SailM LogicalOp := do
  (internal_pick_at (ℓ.child 0) [LogicalOp_AND, LogicalOp_EOR, LogicalOp_ORR])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def LogicalOp_of_num (arg_ : Nat) : LogicalOp :=
  match arg_ with
  | 0 => LogicalOp_AND
  | 1 => LogicalOp_EOR
  | _ => LogicalOp_ORR


def num_of_LogicalOp (arg_ : LogicalOp) : Int :=
  match arg_ with
  | .LogicalOp_AND => 0
  | .LogicalOp_EOR => 1
  | .LogicalOp_ORR => 2


end ArmFull.Functions
