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

def Mk_POR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_POR_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_POR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def AArch64_AddrTop (tbid : (BitVec 1)) (acctype : AccessType) (tbi : (BitVec 1)) : Int :=
  if (((tbid == 1#1) && (BEq.beq acctype AccessType_IFETCH)) : Bool)
  then 63
  else
    (if ((tbi == 1#1) : Bool)
    then 55
    else 63)


def undefined_MECID_P0_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MECID_P0_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_MECID_P0_EL2_Type_MECID (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _update_MECID_P0_EL2_Type_MECID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_MECID_A0_EL2_Type_MECID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_MECID_A1_EL2_Type_MECID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_MECID_P1_EL2_Type_MECID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_MECID_RL_A_EL3_Type_MECID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_VMECID_A_EL2_Type_MECID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_VMECID_P_EL2_Type_MECID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _get_MECID_A0_EL2_Type_MECID (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _get_MECID_A1_EL2_Type_MECID (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _get_MECID_P1_EL2_Type_MECID (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _get_MECID_RL_A_EL3_Type_MECID (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _get_VMECID_A_EL2_Type_MECID (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _get_VMECID_P_EL2_Type_MECID (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def undefined_VMECID_P_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_VMECID_P_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_MECID_A0_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MECID_A0_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_MECID_A1_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MECID_A1_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_MECID_P1_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MECID_P1_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_MECID_RL_A_EL3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MECID_RL_A_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def AArch64_IASize (txsz : (BitVec 6)) : Int :=
  (64 -i (BitVec.toNat txsz))


/-- Type quantifiers: k_N : Nat, List.elem k_N [64, 128] -/
def AArch64_S1AMECFault (walkparams : S1TTWParams) (paspace : PASpace) (regime : Regime) (descriptor : (BitVec k_N)) : SailM Bool := do
  ArmFull.assert (((Sail.BitVec.length descriptor) == 64) || ((Sail.BitVec.length descriptor) == 128)) "sail-arm/v8_base.sail:25140.31-25140.32"
  let descriptor_amec ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (do
        ArmFull.assert (103 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25142.35-25142.36"
        (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 103)])))))
    else (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 63)])))) ) : SailM
    (BitVec 1) )
  (pure ((((((walkparams.emec +++ walkparams.amec) == 0b10#2) && ((BEq.beq regime Regime_EL2) || (BEq.beq
              regime Regime_EL20))) && (BEq.beq paspace PAS_Realm)) && (descriptor_amec == 1#1))))


/-- Type quantifiers: k_N : Nat, level : Int, 52 < k_N -/
def AArch64_ContiguousBit (tgx : TGx) (d128 : (BitVec 1)) (level : Int) (descriptor : (BitVec k_N)) : SailM (BitVec 1) := do
  if ((d128 == 1#1) : Bool)
  then
    (do
      if ((((BEq.beq tgx TGx_64KB) && (level == 1)) || ((BEq.beq tgx TGx_4KB) && (level == 0))) : Bool)
      then (pure (0#1))
      else
        (do
          ArmFull.assert (111 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25301.39-25301.40"
          (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 111)]))))))
  else
    (pure (if (((BEq.beq tgx TGx_64KB) && (level == 1)) : Bool)
      then 0#1
      else
        (if (((BEq.beq tgx TGx_16KB) && (level == 1)) : Bool)
        then 0#1
        else
          (if (((BEq.beq tgx TGx_4KB) && (level == 0)) : Bool)
          then 0#1
          else (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 52)]))))))


def undefined_S2PIR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_S2PIR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_VSTCR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_VSTCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_VSTCR_EL2_Type_SW (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _update_VSTCR_EL2_Type_SW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _update_FPSID_Type_SW (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)


def _update_PMUSERENR_EL0_Type_SW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_PMUSERENR_Type_SW (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_FPSID_Type_SW (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)


def _get_PMUSERENR_EL0_Type_SW (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_PMUSERENR_Type_SW (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def undefined_VSTTBR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_VSTTBR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_S2POR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_S2POR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_VMECID_A_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_VMECID_A_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def AArch64_SS2OutputPASpace (walkparams : S2TTWParams) (ipaspace : PASpace) : PASpace :=
  if ((BEq.beq ipaspace PAS_Secure) : Bool)
  then
    (if (((walkparams.sw +++ walkparams.sa) == 0b00#2) : Bool)
    then PAS_Secure
    else PAS_NonSecure)
  else
    (if (((walkparams.sw +++ (walkparams.sa +++ (walkparams.nsw +++ walkparams.nsa))) == 0b0000#4) : Bool)
    then PAS_Secure
    else PAS_NonSecure)


def S2TLBCache (tlbrecord : TLBRecord) : Unit :=
  ()


def S1TLBCache (tlbrecord : TLBRecord) : Unit :=
  ()


/-- Type quantifiers: counter_index : Nat, 0 ≤ counter_index ∧ counter_index < 32 -/
def SPEStopCounter (counter_index : Nat) : SailM Unit := do
  let w__0 ← (( do readReg SPESampleCounterValid ) : SailM (Vector Bool 32) )
  writeReg SPESampleCounterValid (vectorUpdate w__0 counter_index true)
  let w__1 ← (( do readReg SPESampleCounterPending ) : SailM (Vector Bool 32) )
  writeReg SPESampleCounterPending (vectorUpdate w__1 counter_index false)


def end_translation (desc : AddressDescriptor) : SailM Unit := do
  (sail_translation_end desc)


def start_translation (tsi : TranslationStartInfo) : SailM Unit := do
  (sail_translation_start tsi)


/-- Type quantifiers: processorid : Int, size : Int -/
def ClearExclusiveByAddress (paddress : FullAddress) (processorid : Int) (size : Int) : Unit :=
  ()


def undefined_RCWMASK_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 128) := do
  (undefined_bitvector_at (ℓ.child 0) 128)


def Mk_RCWMASK_EL1_Type (v : (BitVec 128)) : (BitVec 128) :=
  v


def _get_RCWMASK_EL1_Type_Mask (v : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.extractLsb v 127 0)


def _update_RCWMASK_EL1_Type_Mask (v : (BitVec 128)) (x : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 127 0 x)


def undefined_RCWSMASK_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 128) := do
  (undefined_bitvector_at (ℓ.child 0) 128)


def Mk_RCWSMASK_EL1_Type (v : (BitVec 128)) : (BitVec 128) :=
  v


def _get_RCWSMASK_EL1_Type_Software_Mask (v : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.extractLsb v 127 0)


def _update_RCWSMASK_EL1_Type_Software_Mask (v : (BitVec 128)) (x : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 127 0 x)


def AArch64_AllocationTagFromAddress (tagged_address : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb tagged_address 59 56)


def undefined_VNCR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_VNCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


/-- Type quantifiers: processorid : Int, size : Int -/
def AArch64_MarkExclusiveVA (address : (BitVec 64)) (processorid : Int) (size : Int) : Unit :=
  ()


/-- Type quantifiers: processorid : Int, size : Int -/
def MarkExclusiveGlobal (paddress : FullAddress) (processorid : Int) (size : Int) : Unit :=
  ()


/-- Type quantifiers: processorid : Int, size : Int -/
def MarkExclusiveLocal (paddress : FullAddress) (processorid : Int) (size : Int) : Unit :=
  ()


/-- Type quantifiers: processorid : Int, size : Int -/
def AArch64_IsExclusiveVA (address : (BitVec 64)) (processorid : Int) (size : Int) : Bool :=
  true


/-- Type quantifiers: processorid : Int, size : Int -/
def IsExclusiveGlobal (paddress : FullAddress) (processorid : Int) (size : Int) : SailM Bool := do
  (undefined_bool_at (← occLabel 1679) ())


/-- Type quantifiers: processorid : Int, size : Int -/
def IsExclusiveLocal (paddress : FullAddress) (processorid : Int) (size : Int) : SailM Bool := do
  (undefined_bool_at (← occLabel 1680) ())


/-- Type quantifiers: k_N : Nat, e : Int, esize : Int, k_N ≥ 0 -/
def ActivePredicateElement (pred : (BitVec k_N)) (e : Int) (esize : Int) : SailM Bool := do
  ArmFull.assert ((esize == 8) || ((esize == 16) || ((esize == 32) || ((esize == 64) || (esize == 128))))) "sail-arm/v8_base.sail:29766.78-29766.79"
  let n : Int := (e *i (Int.ediv (Sail.Int.toNatChecked (esize)) 8))
  ArmFull.assert ((n ≥b 0) && (n <b (Sail.BitVec.length pred))) "sail-arm/v8_base.sail:29768.26-29768.27"
  (pure (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access pred (Sail.Int.toNatChecked (n)))])) == 1#1)))


/-- Type quantifiers: k_N : Nat, e : Int, esize : Int, k_N ≥ 0 -/
def PredicateElement (pred : (BitVec k_N)) (e : Int) (esize : Int) : SailM (BitVec 1) := do
  ArmFull.assert ((esize == 8) || ((esize == 16) || ((esize == 32) || ((esize == 64) || (esize == 128))))) "sail-arm/v8_base.sail:29776.78-29776.79"
  let n : Int := (e *i (Int.ediv (Sail.Int.toNatChecked (esize)) 8))
  ArmFull.assert ((n ≥b 0) && (n <b (Sail.BitVec.length pred))) "sail-arm/v8_base.sail:29778.26-29778.27"
  (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access pred (Sail.Int.toNatChecked (n)))]))))


/-- Type quantifiers: N : Nat, scale_in : Int, N ≥ 0 -/
def GetOptimizedScale (op : (BitVec k_N)) (scale_in : Int) (N : Nat) : Int :=
  let scale : Int := scale_in
  let scale : Int :=
    if ((N == 16) : Bool)
    then
      (let exp16 : Int := (BitVec.toNat (Sail.BitVec.extractLsb op 14 10))
      let scale : Int :=
        if (((scale +i exp16) <b (Neg.neg 11)) : Bool)
        then ((Neg.neg 11) -i exp16)
        else scale
      if (((scale +i exp16) >b 43) : Bool)
      then (43 -i exp16)
      else scale)
    else
      (if ((N == 32) : Bool)
      then
        (let exp32 : Int := (BitVec.toNat (Sail.BitVec.extractLsb op 30 23))
        let scale : Int :=
          if (((scale +i exp32) <b (Neg.neg 24)) : Bool)
          then ((Neg.neg 24) -i exp32)
          else scale
        if (((scale +i exp32) >b 280) : Bool)
        then (280 -i exp32)
        else scale)
      else
        (if ((N == 64) : Bool)
        then
          (let exp64 : Int := (BitVec.toNat (Sail.BitVec.extractLsb op 62 52))
          let scale : Int :=
            if (((scale +i exp64) <b (Neg.neg 53)) : Bool)
            then ((Neg.neg 53) -i exp64)
            else scale
          if (((scale +i exp64) >b 2101) : Bool)
          then (2101 -i exp64)
          else scale)
        else scale))
  let scale : Int := scale
  scale


/-- Type quantifiers: esize : Int, shift : Int -/
def ShiftSat (shift : Int) (esize : Int) : Int :=
  if ((shift >b (esize +i 1)) : Bool)
  then (esize +i 1)
  else
    (if ((shift <b (Neg.neg (esize +i 1))) : Bool)
    then (Neg.neg (esize +i 1))
    else shift)


/-- Type quantifiers: width : Nat, width = 512 -/
def ZT0_read (width : Nat) : SailM (BitVec width) := do
  ArmFull.assert (width == 512) "sail-arm/v8_base.sail:31298.23-31298.24"
  let w__0 ← (( do readReg _ZT0 ) : SailM (BitVec 512) )
  (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__0 (Sail.Int.toNatChecked ((width -i 1)))
      0))))


/-- Type quantifiers: width : Nat, width = 512 -/
def ZT0_set (width : Nat) (value_name : (BitVec width)) : SailM Unit := do
  ArmFull.assert (width == 512) "sail-arm/v8_base.sail:31305.23-31305.24"
  let w__0 ← (( do readReg _ZT0 ) : SailM (BitVec 512) )
  writeReg _ZT0 (Sail.BitVec.castWidth (m := 512) (Sail.BitVec.updateSubrange w__0
    (Sail.Int.toNatChecked ((width -i 1))) 0 (Sail.BitVec.castWidth value_name)))


/-- Type quantifiers: count : Int, elements : Int, k_invert : Bool -/
def PredCountTest (elements : Int) (count : Int) (invert : Bool) : SailM (BitVec 4) := do
  let c ← (( do (undefined_bitvector_at (← occLabel 1756) 1) ) : SailM (BitVec 1) )
  let n ← (( do (undefined_bitvector_at (← occLabel 1757) 1) ) : SailM (BitVec 1) )
  let z : (BitVec 1) :=
    if ((count == 0) : Bool)
    then 1#1
    else 0#1
  let (c, n) : ((BitVec 1) × (BitVec 1)) :=
    if ((! invert) : Bool)
    then
      (let n : (BitVec 1) :=
        if ((count != 0) : Bool)
        then 1#1
        else 0#1
      let c : (BitVec 1) :=
        if ((count == elements) : Bool)
        then 0#1
        else 1#1
      (c, n))
    else
      (let n : (BitVec 1) :=
        if ((count == elements) : Bool)
        then 1#1
        else 0#1
      let c : (BitVec 1) :=
        if ((count != 0) : Bool)
        then 0#1
        else 1#1
      (c, n))
  let v : (BitVec 1) := 0#1
  (pure ((((n +++ z) +++ c) +++ v)))


def GCSSynchronizationBarrier (_ : Unit) : Unit :=
  ()


def undefined_HFGITR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_HFGITR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_HFGITR_EL2_Type_ATS1E0R (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _update_HFGITR_EL2_Type_ATS1E0R (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _get_HFGITR_EL2_Type_ATS1E0W (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _update_HFGITR_EL2_Type_ATS1E0W (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _get_HFGITR_EL2_Type_ATS1E1R (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _update_HFGITR_EL2_Type_ATS1E1R (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _get_HFGITR_EL2_Type_ATS1E1RP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _update_HFGITR_EL2_Type_ATS1E1RP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _get_HFGITR_EL2_Type_ATS1E1W (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _update_HFGITR_EL2_Type_ATS1E1W (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _get_HFGITR_EL2_Type_ATS1E1WP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _update_HFGITR_EL2_Type_ATS1E1WP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _get_HFGITR_EL2_Type_CFPRCTX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 48 48)


def _update_HFGITR_EL2_Type_CFPRCTX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)


def _get_HFGITR_EL2_Type_COSPRCTX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)


def _update_HFGITR_EL2_Type_COSPRCTX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)


def _get_HFGITR_EL2_Type_CPPRCTX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 50 50)


def _update_HFGITR_EL2_Type_CPPRCTX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 50 50 x)


def _get_HFGITR_EL2_Type_DCCISW (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _update_HFGITR_EL2_Type_DCCISW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _get_HFGITR_EL2_Type_DCCIVAC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _update_HFGITR_EL2_Type_DCCIVAC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _get_HFGITR_EL2_Type_DCCSW (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _update_HFGITR_EL2_Type_DCCSW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _get_HFGITR_EL2_Type_DCCVAC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 54 54)


def _update_HFGITR_EL2_Type_DCCVAC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)


def _get_HFGITR_EL2_Type_DCCVADP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def _update_HFGITR_EL2_Type_DCCVADP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


def _get_HFGITR_EL2_Type_DCCVAP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)


def _update_HFGITR_EL2_Type_DCCVAP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)


def _get_HFGITR_EL2_Type_DCCVAU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _update_HFGITR_EL2_Type_DCCVAU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _get_HFGITR_EL2_Type_DCISW (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _update_HFGITR_EL2_Type_DCISW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_HFGITR_EL2_Type_DCIVAC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_HFGITR_EL2_Type_DCIVAC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_HFGITR_EL2_Type_DCZVA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)


def _update_HFGITR_EL2_Type_DCZVA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _get_HFGITR_EL2_Type_DVPRCTX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 49 49)


def _update_HFGITR_EL2_Type_DVPRCTX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 49 x)


def _get_HFGITR_EL2_Type_ERET (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 51 51)


def _update_HFGITR_EL2_Type_ERET (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 51 x)


def _get_HFGITR_EL2_Type_ICIALLU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_HFGITR_EL2_Type_ICIALLU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_HFGITR_EL2_Type_ICIALLUIS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_HFGITR_EL2_Type_ICIALLUIS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_HFGITR_EL2_Type_ICIVAU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_HFGITR_EL2_Type_ICIVAU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_HFGITR_EL2_Type_SVC_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 52 52)


def _update_HFGITR_EL2_Type_SVC_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)


def _get_HFGITR_EL2_Type_SVC_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 53 53)


def _update_HFGITR_EL2_Type_SVC_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 53 x)


def _get_HFGITR_EL2_Type_TLBIASIDE1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 44 44)


def _update_HFGITR_EL2_Type_TLBIASIDE1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)


def _get_HFGITR_EL2_Type_TLBIASIDE1IS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _update_HFGITR_EL2_Type_TLBIASIDE1IS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _get_HFGITR_EL2_Type_TLBIASIDE1OS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def _update_HFGITR_EL2_Type_TLBIASIDE1OS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def _get_HFGITR_EL2_Type_TLBIRVAAE1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 39 39)


def _update_HFGITR_EL2_Type_TLBIRVAAE1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 39 x)


def _get_HFGITR_EL2_Type_TLBIRVAAE1IS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 35 35)


def _update_HFGITR_EL2_Type_TLBIRVAAE1IS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 35 x)


def _get_HFGITR_EL2_Type_TLBIRVAAE1OS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)


def _update_HFGITR_EL2_Type_TLBIRVAAE1OS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)


def _get_HFGITR_EL2_Type_TLBIRVAALE1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 41 41)


def _update_HFGITR_EL2_Type_TLBIRVAALE1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 41 x)


def _get_HFGITR_EL2_Type_TLBIRVAALE1IS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)


def _update_HFGITR_EL2_Type_TLBIRVAALE1IS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)


end ArmFull.Functions
