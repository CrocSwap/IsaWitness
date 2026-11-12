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

def C47PickLS64UNSUPPORTED (_ : Unit) : SailM Constraint := do
  let rank ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 1198) 0 1))) ) :
    SailM Nat )
  (pure (if ((rank == 0) : Bool)
    then Constraint_FAULT
    else Constraint_LIMITED_ATOMICITY))


def C47PickMOPSOVERLAP31 (_ : Unit) : SailM Constraint := do
  let rank ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 1199) 0 1))) ) :
    SailM Nat )
  (pure (if ((rank == 0) : Bool)
    then Constraint_NOP
    else Constraint_UNDEF))


def C47PickNVNV1 (_ : Unit) : SailM Constraint := do
  let rank ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 1200) 0 2))) ) :
    SailM Nat )
  (pure (if ((rank == 0) : Bool)
    then Constraint_NVNV1_00
    else
      (if ((rank == 1) : Bool)
      then Constraint_NVNV1_01
      else Constraint_NVNV1_11)))


def C47PickRESBPMASK (_ : Unit) : SailM Constraint := do
  let rank ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 1201) 0 2))) ) :
    SailM Nat )
  (pure (if ((rank == 0) : Bool)
    then Constraint_DISABLED
    else
      (if ((rank == 1) : Bool)
      then Constraint_NONE
      else Constraint_UNKNOWN)))


def C47PickRESTnSZ (_ : Unit) : SailM Constraint := do
  let rank ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 1202) 0 1))) ) :
    SailM Nat )
  (pure (if ((rank == 0) : Bool)
    then Constraint_FORCE
    else Constraint_NONE))


def C47PickRESWPMASK (_ : Unit) : SailM Constraint := do
  let rank ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 1203) 0 2))) ) :
    SailM Nat )
  (pure (if ((rank == 0) : Bool)
    then Constraint_DISABLED
    else
      (if ((rank == 1) : Bool)
      then Constraint_NONE
      else Constraint_UNKNOWN)))


def C47PickS2RESMEMATTR (_ : Unit) : SailM Constraint := do
  let rank ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 1204) 0 2))) ) :
    SailM Nat )
  (pure (if ((rank == 0) : Bool)
    then Constraint_NC
    else
      (if ((rank == 1) : Bool)
      then Constraint_WT
      else Constraint_WB)))


def C47PickSMD (_ : Unit) : SailM Constraint := do
  let rank ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 1205) 0 1))) ) :
    SailM Nat )
  (pure (if ((rank == 0) : Bool)
    then Constraint_NOP
    else Constraint_UNDEF))


def C47PickShareability (_ : Unit) : SailM Constraint := do
  let rank ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 1206) 0 2))) ) :
    SailM Nat )
  (pure (if ((rank == 0) : Bool)
    then Constraint_OSH
    else
      (if ((rank == 1) : Bool)
      then Constraint_ISH
      else Constraint_NSH)))


def C47PickVMSR (_ : Unit) : SailM Constraint := do
  let rank ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 1207) 0 1))) ) :
    SailM Nat )
  (pure (if ((rank == 0) : Bool)
    then Constraint_NOP
    else Constraint_UNDEF))


def C47PickWBOVERLAPLD (_ : Unit) : SailM Constraint := do
  let rank ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 1208) 0 3))) ) :
    SailM Nat )
  (pure (if ((rank == 0) : Bool)
    then Constraint_NOP
    else
      (if ((rank == 1) : Bool)
      then Constraint_UNDEF
      else
        (if ((rank == 2) : Bool)
        then Constraint_UNKNOWN
        else Constraint_WBSUPPRESS))))


def C47PickWBOVERLAPST (_ : Unit) : SailM Constraint := do
  let rank ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 1209) 0 3))) ) :
    SailM Nat )
  (pure (if ((rank == 0) : Bool)
    then Constraint_NONE
    else
      (if ((rank == 1) : Bool)
      then Constraint_NOP
      else
        (if ((rank == 2) : Bool)
        then Constraint_UNDEF
        else Constraint_UNKNOWN))))


def S2CombineS1Shareability (s1_shareability : Shareability) (s2_shareability : Shareability) : Shareability :=
  if (((BEq.beq s1_shareability Shareability_OSH) || (BEq.beq s2_shareability Shareability_OSH)) : Bool)
  then Shareability_OSH
  else
    (if (((BEq.beq s1_shareability Shareability_ISH) || (BEq.beq s2_shareability Shareability_ISH)) : Bool)
    then Shareability_ISH
    else Shareability_NSH)


def S2CombineS1Device (s1_device : DeviceType) (s2_device : DeviceType) : DeviceType :=
  if (((BEq.beq s1_device DeviceType_nGnRnE) || (BEq.beq s2_device DeviceType_nGnRnE)) : Bool)
  then DeviceType_nGnRnE
  else
    (if (((BEq.beq s1_device DeviceType_nGnRE) || (BEq.beq s2_device DeviceType_nGnRE)) : Bool)
    then DeviceType_nGnRE
    else
      (if (((BEq.beq s1_device DeviceType_nGRE) || (BEq.beq s2_device DeviceType_nGRE)) : Bool)
      then DeviceType_nGRE
      else DeviceType_GRE))


def undefined_GPCCR_EL3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_GPCCR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_GPCCR_EL3_Type_GPC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _update_GPCCR_EL3_Type_GPC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _get_GPCCR_EL3_Type_GPCP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _update_GPCCR_EL3_Type_GPCP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _get_GPCCR_EL3_Type_L0GPTSZ (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _update_GPCCR_EL3_Type_L0GPTSZ (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _get_GPCCR_EL3_Type_ORGN (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)


def _update_GPCCR_EL3_Type_ORGN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)


def _get_GPCCR_EL3_Type_PGS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _update_GPCCR_EL3_Type_PGS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _get_GPCCR_EL3_Type_PPS (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)


def _update_GPCCR_EL3_Type_PPS (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 0 x)


def undefined_GPTBR_EL3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_GPTBR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def GPTTLBCache (pgs : PGSe) (gpt_entry : GPTEntry) : Unit :=
  ()


def undefined_GICC_CTLR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def GIC_PENDING_NONE : (BitVec 32) := 0x000003FF#32


def AccessDescriptor_to_Access_kind (accdesc : AccessDescriptor) : (Access_kind arm_acc_type) :=
  match accdesc.acctype with
  | .AccessType_IFETCH => (AK_ifetch ())
  | .AccessType_GPR =>
    (let variety :=
      if (accdesc.exclusive : Bool)
      then AV_exclusive
      else
        (if (accdesc.atomicop : Bool)
        then AV_atomic_rmw
        else AV_plain)
    let strength :=
      if (accdesc.acqpc : Bool)
      then AS_acq_rcpc
      else
        (if ((accdesc.acqsc || accdesc.relsc) : Bool)
        then AS_rel_or_acq
        else AS_normal)
    (AK_explicit
      { variety := variety
        strength := strength }))
  | .AccessType_TTW => (AK_ttw ())
  | .AccessType_ASIMD => (AK_arch (SAcc_ASIMD accdesc.streamingsve))
  | .AccessType_SVE => (AK_arch (SAcc_SVE accdesc.streamingsve))
  | .AccessType_SME => (AK_arch (SAcc_SME accdesc.streamingsve))
  | .AccessType_IC => (AK_arch (SAcc_IC ()))
  | .AccessType_DC => (AK_arch (SAcc_DC ()))
  | .AccessType_DCZero => (AK_arch (SAcc_DCZero ()))
  | .AccessType_AT => (AK_arch (SAcc_AT ()))
  | .AccessType_NV2 => (AK_arch (SAcc_NV2 ()))
  | .AccessType_SPE => (AK_arch (SAcc_SPE ()))
  | .AccessType_GCS => (AK_arch (SAcc_GCS ()))
  | .AccessType_GPTW => (AK_arch (SAcc_GPTW ()))


def GIC_BASE := 0x2C00#16


def __GICC_IIDR := 0x0002043B#32


def UART_BASE := 0x3C00#16


/-- Type quantifiers: gpt_range : Int -/
def SetTLBIncludesGPT (context : TLBContext) (gpt_range : Int) : Unit :=
  ()


/-- Type quantifiers: level : Int -/
def ContiguousSize (d128 : (BitVec 1)) (tgx : TGx) (level : Int) : SailM Int := do
  if ((d128 == 1#1) : Bool)
  then
    (do
      match tgx with
      | .TGx_4KB =>
        (do
          ArmFull.assert ((level == 1) || ((level == 2) || (level == 3))) "sail-arm/v8_base.sail:19968.57-19968.58"
          (pure (if ((level == 1) : Bool)
            then 2
            else 4)))
      | .TGx_16KB =>
        (do
          ArmFull.assert ((level == 1) || ((level == 2) || (level == 3))) "sail-arm/v8_base.sail:19972.57-19972.58"
          (pure (if ((level == 1) : Bool)
            then 2
            else
              (if ((level == 2) : Bool)
              then 4
              else 6))))
      | .TGx_64KB =>
        (do
          ArmFull.assert ((level == 2) || (level == 3)) "sail-arm/v8_base.sail:19982.44-19982.45"
          (pure (if ((level == 2) : Bool)
            then 6
            else 4))))
  else
    (do
      match tgx with
      | .TGx_4KB =>
        (do
          ArmFull.assert ((level == 1) || ((level == 2) || (level == 3))) "sail-arm/v8_base.sail:19992.57-19992.58"
          (pure (4)))
      | .TGx_16KB =>
        (do
          ArmFull.assert ((level == 2) || (level == 3)) "sail-arm/v8_base.sail:19996.44-19996.45"
          (pure (if ((level == 2) : Bool)
            then 5
            else 7)))
      | .TGx_64KB =>
        (do
          ArmFull.assert ((level == 2) || (level == 3)) "sail-arm/v8_base.sail:20000.44-20000.45"
          (pure (5))))


def TGxGranuleBits (tgx : TGx) : Int :=
  match tgx with
  | .TGx_4KB => 12
  | .TGx_16KB => 14
  | .TGx_64KB => 16


def HasUnprivileged (regime : Regime) : Bool :=
  ((BEq.beq regime Regime_EL20) || ((BEq.beq regime Regime_EL30) || (BEq.beq regime Regime_EL10)))


def AArch64_GetVARange (va : (BitVec 64)) : VARange :=
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access va 55)])) == 0#1) : Bool)
  then VARange_LOWER
  else VARange_UPPER


def undefined_MAIR2_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MAIR2_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_MAIR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MAIR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_PIRE0_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_PIRE0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_PIR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_PIR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_TCR2_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_TCR2_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_TCR2_EL1_Type_DisCH1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _update_TCR2_EL1_Type_DisCH1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _update_TCR2_EL2_Type_DisCH1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _get_TCR2_EL2_Type_DisCH1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def undefined_MAIR2_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MAIR2_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_MAIR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MAIR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_PIR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_PIR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_TCR2_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_TCR2_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_TCR2_EL2_Type_AMEC0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _update_TCR2_EL2_Type_AMEC0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _get_TCR2_EL2_Type_AMEC1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _update_TCR2_EL2_Type_AMEC1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _get_TCR2_EL2_Type_SKL0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)


def _update_TCR2_EL2_Type_SKL0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)


def _get_TCR2_EL2_Type_SKL1 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 9 8)


def _update_TCR2_EL2_Type_SKL1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 8 x)


def undefined_PIRE0_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_PIRE0_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_MAIR2_EL3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MAIR2_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_MAIR_EL3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MAIR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_PIR_EL3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_PIR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_SCTLR2_EL3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_SCTLR2_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_TTBR0_EL3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_TTBR0_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def PACCellInvShuffle (indata : (BitVec 64)) : SailM (BitVec 64) := do
  let outdata ← (( do (undefined_bitvector_at (← occLabel 1275) 64) ) : SailM (BitVec 64) )
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 3 0 (Sail.BitVec.extractLsb indata 15 12))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 7 4 (Sail.BitVec.extractLsb indata 27 24))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 11 8 (Sail.BitVec.extractLsb indata 51 48))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 15 12 (Sail.BitVec.extractLsb indata 39 36))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 19 16 (Sail.BitVec.extractLsb indata 59 56))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 23 20 (Sail.BitVec.extractLsb indata 47 44))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 27 24 (Sail.BitVec.extractLsb indata 7 4))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 31 28 (Sail.BitVec.extractLsb indata 19 16))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 35 32 (Sail.BitVec.extractLsb indata 35 32))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 39 36 (Sail.BitVec.extractLsb indata 55 52))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 43 40 (Sail.BitVec.extractLsb indata 31 28))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 47 44 (Sail.BitVec.extractLsb indata 11 8))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 51 48 (Sail.BitVec.extractLsb indata 23 20))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 55 52 (Sail.BitVec.extractLsb indata 3 0))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 59 56 (Sail.BitVec.extractLsb indata 43 40))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 63 60 (Sail.BitVec.extractLsb indata 63 60))
  (pure (outdata))


def PACCellShuffle (indata : (BitVec 64)) : SailM (BitVec 64) := do
  let outdata ← (( do (undefined_bitvector_at (← occLabel 1276) 64) ) : SailM (BitVec 64) )
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 3 0 (Sail.BitVec.extractLsb indata 55 52))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 7 4 (Sail.BitVec.extractLsb indata 27 24))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 11 8 (Sail.BitVec.extractLsb indata 47 44))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 15 12 (Sail.BitVec.extractLsb indata 3 0))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 19 16 (Sail.BitVec.extractLsb indata 31 28))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 23 20 (Sail.BitVec.extractLsb indata 51 48))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 27 24 (Sail.BitVec.extractLsb indata 7 4))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 31 28 (Sail.BitVec.extractLsb indata 43 40))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 35 32 (Sail.BitVec.extractLsb indata 35 32))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 39 36 (Sail.BitVec.extractLsb indata 15 12))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 43 40 (Sail.BitVec.extractLsb indata 59 56))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 47 44 (Sail.BitVec.extractLsb indata 23 20))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 51 48 (Sail.BitVec.extractLsb indata 11 8))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 55 52 (Sail.BitVec.extractLsb indata 39 36))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 59 56 (Sail.BitVec.extractLsb indata 19 16))
  let outdata : (BitVec 64) :=
    (Sail.BitVec.updateSubrange outdata 63 60 (Sail.BitVec.extractLsb indata 63 60))
  (pure (outdata))


/-- Type quantifiers: amount : Nat, 0 ≤ (4 - amount) ∧ (7 - amount) < 8 -/
def RotCell (incell_name : (BitVec 4)) (amount : Nat) : SailM (BitVec 4) := do
  let tmp ← (( do (undefined_bitvector_at (← occLabel 1278) 8) ) : SailM (BitVec 8) )
  let tmp : (BitVec 8) :=
    (Sail.BitVec.updateSubrange tmp 7 0
      ((Sail.BitVec.extractLsb incell_name 3 0) +++ (Sail.BitVec.extractLsb incell_name 3 0)))
  let outcell : (BitVec 4) :=
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb tmp (Sail.Int.toNatChecked ((7 -i amount)))
      (Sail.Int.toNatChecked ((4 -i amount)))))
  (pure (outcell))


/-- Type quantifiers: n : Int, width : Nat, List.elem width [8, 16, 32, 64, 128] -/
def V_read (n : Int) (width : Nat) : SailM (BitVec width) := do
  ArmFull.assert ((n ≥b 0) && (n ≤b 31)) "sail-arm/v8_base.sail:22333.27-22333.28"
  ArmFull.assert ((width == 8) || ((width == 16) || ((width == 32) || ((width == 64) || (width == 128))))) "sail-arm/v8_base.sail:22334.78-22334.79"
  let w__0 ← (( do readReg _Z ) : SailM (Vector (BitVec 2048) 32) )
  (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb
      (GetElem?.getElem! w__0 (Sail.Int.toNatChecked (n))) (Sail.Int.toNatChecked ((width -i 1))) 0))))


def undefined_CNTKCTL_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_CNTKCTL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_CNTKCTL_Type_PL0PCTEN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_CNTKCTL_Type_PL0PCTEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_CNTKCTL_Type_PL0PTEN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def _update_CNTKCTL_Type_PL0PTEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


def _get_CNTKCTL_Type_PL0VCTEN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_CNTKCTL_Type_PL0VCTEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_CNTKCTL_Type_PL0VTEN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)


def _update_CNTKCTL_Type_PL0VTEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)


def CNTKCTL_read__1 (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CNTKCTL ) : SailM CNTKCTL_Type )
  let w__0 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


/-- Type quantifiers: k_guardedpage : Bool -/
def SetInGuardedPage (guardedpage : Bool) : SailM Unit := do
  writeReg InGuardedPage guardedpage


def BTypeCompatible_BTI (hintcode : (BitVec 2)) : SailM Bool := do
  match hintcode with
  | 0b00 => (pure (false))
  | 0b01 =>
    (do
      let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
      (pure ((w__0.BTYPE != 0b11#2))))
  | 0b10 =>
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      (pure ((w__1.BTYPE != 0b10#2))))
  | 0b11 => (pure (true))
  | _ =>
    (do
      (undefined_bool_at (← occLabel 1345) ()))


/-- Type quantifiers: k_x : Bool -/
def SetBTypeCompatible (x : Bool) : SailM Unit := do
  writeReg BTypeCompatible x


def SetBTypeNext (x : (BitVec 2)) : SailM Unit := do
  writeReg BTypeNext x


def undefined_GCR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_GCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_GCR_EL1_Type_Exclude (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _update_GCR_EL1_Type_Exclude (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _get_GCR_EL1_Type_RRND (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _update_GCR_EL1_Type_RRND (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def undefined_RGSR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


end ArmFull.Functions
