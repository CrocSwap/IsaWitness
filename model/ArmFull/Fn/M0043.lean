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

def _update_SCTLR_EL1_Type_EnIB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_SCTLR_EL3_Type_EnIB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _get_SCTLR_EL1_Type_EnIB (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_SCTLR_EL3_Type_EnIB (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_SCTLR_EL2_Type_EnRCTX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _update_SCTLR_EL2_Type_EnRCTX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _update_SCTLR_EL1_Type_EnRCTX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _update_SCTLR_Type_EnRCTX (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _get_SCTLR_EL1_Type_EnRCTX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _get_SCTLR_Type_EnRCTX (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _get_SCTLR_EL2_Type_ITFSB (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)


def _update_SCTLR_EL2_Type_ITFSB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)


def _update_SCTLR_EL1_Type_ITFSB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)


def _update_SCTLR_EL3_Type_ITFSB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)


def _get_SCTLR_EL1_Type_ITFSB (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)


def _get_SCTLR_EL3_Type_ITFSB (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)


def _get_SCTLR_EL2_Type_MSCEn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)


def _update_SCTLR_EL2_Type_MSCEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)


def _update_HCRX_EL2_Type_MSCEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _update_SCTLR_EL1_Type_MSCEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)


def _get_HCRX_EL2_Type_MSCEn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)


def _get_SCTLR_EL1_Type_MSCEn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)


def _get_SCTLR_EL2_Type_TCF (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 41 40)


def _update_SCTLR_EL2_Type_TCF (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 40 x)


def _update_SCTLR_EL1_Type_TCF (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 40 x)


def _update_SCTLR_EL3_Type_TCF (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 40 x)


def _get_SCTLR_EL1_Type_TCF (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 41 40)


def _get_SCTLR_EL3_Type_TCF (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 41 40)


def _get_SCTLR_EL2_Type_TCF0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 39 38)


def _update_SCTLR_EL2_Type_TCF0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 38 x)


def _update_SCTLR_EL1_Type_TCF0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 38 x)


def _get_SCTLR_EL1_Type_TCF0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 39 38)


def _get_SCTLR_EL2_Type_TCSO (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)


def _update_SCTLR_EL2_Type_TCSO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)


def _update_SCTLR_EL1_Type_TCSO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)


def _update_SCTLR_EL3_Type_TCSO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)


def _get_SCTLR_EL1_Type_TCSO (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)


def _get_SCTLR_EL3_Type_TCSO (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)


def _get_SCTLR_EL2_Type_TCSO0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)


def _update_SCTLR_EL2_Type_TCSO0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)


def _update_SCTLR_EL1_Type_TCSO0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)


def _get_SCTLR_EL1_Type_TCSO0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)


def HSCTLR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HSCTLR ) : SailM HSCTLR_Type )
  let w__0 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def undefined_SCTLR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_SCTLR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_SCTLR_EL1_Type_BT1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 36 36)


def _update_SCTLR_EL1_Type_BT1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)


def undefined_SCTLR_EL3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_SCTLR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_SCTLR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_SCTLR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_SCTLR_Type_AFE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _update_SCTLR_Type_AFE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _get_SCTLR_Type_TRE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _update_SCTLR_Type_TRE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _get_SCTLR_Type_UNK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _update_SCTLR_Type_UNK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _get_SCTLR_Type_UWXN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def _update_SCTLR_Type_UWXN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def SCTLR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _SCTLR_NS ) : SailM SCTLR_Type )
  let w__0 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def ConditionHolds (cond : (BitVec 4)) : SailM Bool := do
  let result ← (( do (undefined_bool_at (← occLabel 669) ()) ) : SailM Bool )
  let result ← (( do
    match (BitVec.setWidth 3 (Sail.BitVec.extractLsb cond 3 1)) with
    | 0b000 =>
      (do
        let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
        let result := ((w__0.Z == 1#1) : Bool)
        (pure (result)))
    | 0b001 =>
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        let result := ((w__1.C == 1#1) : Bool)
        (pure (result)))
    | 0b010 =>
      (do
        let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
        let result := ((w__2.N == 1#1) : Bool)
        (pure (result)))
    | 0b011 =>
      (do
        let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
        let result := ((w__3.V == 1#1) : Bool)
        (pure (result)))
    | 0b100 =>
      (do
        if ((← do
             let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__4.C == 1#1) : Bool)))) : Bool)
        then
          (do
            let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__5.Z == 0#1) : Bool))))
        else (pure false))
    | 0b101 =>
      (do
        let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
        let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
        let result := ((w__7.N == w__8.V) : Bool)
        (pure (result)))
    | 0b110 =>
      (do
        if ((← do
             let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
             let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__9.N == w__10.V) : Bool)))) : Bool)
        then
          (do
            let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__11.Z == 0#1) : Bool))))
        else (pure false))
    | _ => (pure (true)) ) : SailM Bool )
  let result : Bool :=
    if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access cond 0)])) == 1#1) && (cond != 0b1111#4)) : Bool)
    then (! result)
    else result
  (pure (result))


def ThisInstrLength (_ : Unit) : SailM Int := do
  let w__0 ← (( do readReg __ThisInstrEnc ) : SailM __InstrEnc )
  let w__1 : Int :=
    if ((BEq.beq w__0 __T16) : Bool)
    then 16
    else 32
  (pure (w__1))


def undefined_ESR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_ESR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ESR_EL1_Type_ISS2 (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 55 32)


def _update_ESR_EL1_Type_ISS2 (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 32 x)


def _update_ESR_EL2_Type_ISS2 (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 32 x)


def _update_ESR_EL3_Type_ISS2 (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 32 x)


def _get_ESR_EL2_Type_ISS2 (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 55 32)


def _get_ESR_EL3_Type_ISS2 (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 55 32)


def undefined_ESR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_ESR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_ESR_EL3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_ESR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_HPFAR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_HPFAR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_HPFAR_EL2_Type_FIPA (v : (BitVec 64)) : (BitVec 44) :=
  (Sail.BitVec.extractLsb v 47 4)


def _update_HPFAR_EL2_Type_FIPA (v : (BitVec 64)) (x : (BitVec 44)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 4 x)


def _update_HPFAR_Type_FIPA (v : (BitVec 32)) (x : (BitVec 28)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 4 x)


def _get_HPFAR_Type_FIPA (v : (BitVec 32)) : (BitVec 28) :=
  (Sail.BitVec.extractLsb v 31 4)


def undefined_MFAR_EL3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MFAR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_MFAR_EL3_Type_FPA (v : (BitVec 64)) : (BitVec 44) :=
  ((Sail.BitVec.extractLsb v 55 52) +++ ((Sail.BitVec.extractLsb v 51 48) +++ (Sail.BitVec.extractLsb
        v 47 12)))


def _update_MFAR_EL3_Type_FPA (v : (BitVec 64)) (x : (BitVec 44)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange
      (Sail.BitVec.updateSubrange v 55 52
        (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((44 -i 1)))
          (Sail.Int.toNatChecked ((((44 -i 1) -i ((55 -i 52) +i 1)) +i 1))))) 51 48
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((44 -i 1) -i ((55 -i 52) +i 1))))
        (Sail.Int.toNatChecked (((((44 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1)) +i 1)))))
    47 12
    (Sail.BitVec.extractLsb x
      (Sail.Int.toNatChecked ((((44 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1))))
      (Sail.Int.toNatChecked ((((((44 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1)) -i ((47 -i 12) +i 1)) +i 1)))))


def undefined_PFAR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_PFAR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_PFAR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_PFAR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_SPSR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_SPSR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_SPSR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_SPSR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_SPSR_EL3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_SPSR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_SPSR_abt_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_SPSR_abt_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_SPSR_abt_Type_J (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _update_SPSR_abt_Type_J (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _update_SPSR_fiq_Type_J (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _update_SPSR_hyp_Type_J (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _update_SPSR_irq_Type_J (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _update_SPSR_mon_Type_J (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _update_SPSR_svc_Type_J (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _update_SPSR_und_Type_J (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)


def _get_SPSR_fiq_Type_J (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _get_SPSR_hyp_Type_J (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _get_SPSR_irq_Type_J (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _get_SPSR_mon_Type_J (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _get_SPSR_svc_Type_J (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def _get_SPSR_und_Type_J (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)


def undefined_SPSR_fiq_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_SPSR_fiq_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_SPSR_hyp_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_SPSR_hyp_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def SPSR_hyp_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _SPSR_hyp ) : SailM SPSR_hyp_Type )
  let w__0 ← (( do readReg SPSR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def SPSR_hyp_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : SPSR_hyp_Type := value_name
  let w__0 ← (( do readReg SPSR_EL2 ) : SailM (BitVec 64) )
  writeReg SPSR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _SPSR_hyp r


def undefined_SPSR_irq_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_SPSR_irq_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_SPSR_mon_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_SPSR_mon_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def undefined_SPSR_svc_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_SPSR_svc_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def SPSR_svc_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _SPSR_svc ) : SailM SPSR_svc_Type )
  let w__0 ← (( do readReg SPSR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def SPSR_svc_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : SPSR_svc_Type := value_name
  let w__0 ← (( do readReg SPSR_EL1 ) : SailM (BitVec 64) )
  writeReg SPSR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _SPSR_svc r


def undefined_SPSR_und_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_SPSR_und_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def SynchronizeContext (_ : Unit) : Unit :=
  ()


def SynchronizeErrors (_ : Unit) : Unit :=
  ()


def undefined_EDECCR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_EDECCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_EDECCR_Type_NSE0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _update_EDECCR_Type_NSE0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_EDECCR_Type_NSE1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _update_EDECCR_Type_NSE1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _get_EDECCR_Type_NSE2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _update_EDECCR_Type_NSE2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _get_EDECCR_Type_NSE3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _update_EDECCR_Type_NSE3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _get_EDECCR_Type_NSR0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _update_EDECCR_Type_NSR0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _get_EDECCR_Type_NSR1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _update_EDECCR_Type_NSR1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _get_EDECCR_Type_NSR2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _update_EDECCR_Type_NSR2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _get_EDECCR_Type_NSR3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _update_EDECCR_Type_NSR3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _get_EDECCR_Type_RLE0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _update_EDECCR_Type_RLE0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _get_EDECCR_Type_RLE1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _update_EDECCR_Type_RLE1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _get_EDECCR_Type_RLE2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)


def _update_EDECCR_Type_RLE2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)


def _get_EDECCR_Type_RLR0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def _update_EDECCR_Type_RLR0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def _get_EDECCR_Type_RLR1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


def _update_EDECCR_Type_RLR1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)


def _get_EDECCR_Type_RLR2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _update_EDECCR_Type_RLR2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _get_EDECCR_Type_SE0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_EDECCR_Type_SE0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_EDECCR_Type_SE1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_EDECCR_Type_SE1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_EDECCR_Type_SE2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_EDECCR_Type_SE2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_EDECCR_Type_SE3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_EDECCR_Type_SE3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_EDECCR_Type_SR0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)


def _update_EDECCR_Type_SR0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)


def _get_EDECCR_Type_SR1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def _update_EDECCR_Type_SR1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


def _get_EDECCR_Type_SR2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


end ArmFull.Functions
