module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0052
public import ArmFull.Fn.M0058
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0111
public import ArmFull.Fn.M0121
public import ArmFull.Fn.M0174
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0190
public import ArmFull.Fn.M0194
public import ArmFull.Fn.M0198
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0202
public import ArmFull.Fn.M0203
public import ArmFull.Fn.M0204
public import ArmFull.Fn.M0205
public import ArmFull.Fn.M0206
public import ArmFull.Fn.M0208 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: k_is_load : Bool -/
def SPESampleLoadStore (is_load : Bool) (accdesc : AccessDescriptor) (addrdesc : AddressDescriptor) : SailM Unit := do
  if (((BEq.beq accdesc.acctype AccessType_SPE) || ((BEq.beq accdesc.acctype AccessType_IFETCH) || ((BEq.beq
             accdesc.acctype AccessType_DC) || ((BEq.beq accdesc.acctype AccessType_TTW) || (BEq.beq
               accdesc.acctype AccessType_AT))))) : Bool)
  then (pure (()))
  else
    (do
      let sample_loads ← (( do
        if ((← do
             let w__0 ← (( do readReg SPESampleSubclass ) : SailM (BitVec 8) )
             (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__0 0)])) == 0#1) : Bool)))) : Bool)
        then
          (do
            readReg SPESampleSubclassValid)
        else (pure false) ) : SailM Bool )
      let sample_stores ← (( do
        if ((← do
             let w__2 ← (( do readReg SPESampleSubclass ) : SailM (BitVec 8) )
             (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__2 0)])) == 1#1) : Bool)))) : Bool)
        then
          (do
            readReg SPESampleSubclassValid)
        else (pure false) ) : SailM Bool )
      let w__6 ← (( do
        (pure (((← do
                let w__4 ← (( do readReg SPESampleSubclassValid ) : SailM Bool )
                (pure (((! w__4) : Bool)))) || (sample_loads && is_load)) || (sample_stores && (! is_load))))
        ) : SailM Bool )
      if (w__6 : Bool)
      then
        (do
          (SPESetDataVirtualAddress addrdesc.vaddress)
          let w__7 ← (( do (CollectPhysicalAddress ()) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (SPESetDataPhysicalAddress addrdesc accdesc))
          else (pure (())))
      else (pure (()))
      let w__8 ← (( do readReg SPESampleSubclassValid ) : SailM Bool )
      if ((! w__8) : Bool)
      then
        (do
          writeReg SPESampleClass 0b01#2
          writeReg SPESampleSubclassValid true
          let w__9 ← (( do readReg SPESampleSubclass ) : SailM (BitVec 8) )
          writeReg SPESampleSubclass (Sail.BitVec.updateSubrange w__9 7 1 0b0001000#7)
          let w__10 ← (( do readReg SPESampleSubclass ) : SailM (BitVec 8) )
          writeReg SPESampleSubclass (BitVec.update w__10 0
            (Bit
              (if (is_load : Bool)
              then 0#1
              else 1#1)))
          writeReg SPESampleOpType (if (is_load : Bool)
          then OpType_Load
          else OpType_Store)
          if ((BEq.beq accdesc.acctype AccessType_NV2) : Bool)
          then
            (do
              let w__11 ← (( do readReg SPESampleSubclass ) : SailM (BitVec 8) )
              writeReg SPESampleSubclass (Sail.BitVec.updateSubrange w__11 7 1 0b0011000#7)
              writeReg SPESampleInstIsNV2 true)
          else (pure (())))
      else (pure (())))


/-- Type quantifiers: k_N : Nat, k_soft : Bool, List.elem k_N [64, 128] -/
def RCWCheck (old : (BitVec k_N)) (new : (BitVec k_N)) (soft : Bool) : SailM (BitVec 4) := do
  ArmFull.assert (((Sail.BitVec.length old) == 64) || ((Sail.BitVec.length old) == 128)) "sail-inputs/03-v8_base.sail:28519.31-28519.32"
  let protectedbit : Nat :=
    if (((Sail.BitVec.length old) == 128) : Bool)
    then RCW128_PROTECTED_BIT
    else RCW64_PROTECTED_BIT
  let rcw_fail : Bool := false
  let rcws_fail : Bool := false
  let rcw_state_fail : Bool := false
  let rcws_state_fail : Bool := false
  let rcw_mask_fail : Bool := false
  let rcws_mask_fail : Bool := false
  let w__0 ← (( do readReg RCWMASK_EL1 ) : SailM (BitVec 128) )
  let rcwmask : (BitVec k_N) :=
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__0
      (Sail.Int.toNatChecked (((Sail.BitVec.length old) -i 1))) 0))
  let rcwmask : (BitVec k_N) :=
    if (((Sail.BitVec.length rcwmask) == 64) : Bool)
    then
      (let rcwmask : (BitVec k_N) :=
        (Sail.BitVec.updateSubrange rcwmask 49 18
          (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rcwmask 17)])) 32))
      (BitVec.update rcwmask 0 (Bit 0#1)))
    else
      (let rcwmask : (BitVec k_N) :=
        (Sail.BitVec.updateSubrange rcwmask 55 17
          (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rcwmask 16)])) 39))
      let split_vec := (Zeros (n := 48))
      let rcwmask : (BitVec k_N) :=
        (Sail.BitVec.updateSubrange rcwmask 126 125 (Sail.BitVec.extractLsb split_vec 47 46))
      let rcwmask : (BitVec k_N) :=
        (Sail.BitVec.updateSubrange rcwmask 120 119 (Sail.BitVec.extractLsb split_vec 45 44))
      let rcwmask : (BitVec k_N) :=
        (Sail.BitVec.updateSubrange rcwmask 107 101 (Sail.BitVec.extractLsb split_vec 43 37))
      let rcwmask : (BitVec k_N) :=
        (Sail.BitVec.updateSubrange rcwmask 90 56 (Sail.BitVec.extractLsb split_vec 36 2))
      (Sail.BitVec.updateSubrange rcwmask 1 0 (Sail.BitVec.extractLsb split_vec 1 0)))
  let w__1 ← (( do readReg RCWSMASK_EL1 ) : SailM (BitVec 128) )
  let rcwsoftmask : (BitVec k_N) :=
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__1
      (Sail.Int.toNatChecked (((Sail.BitVec.length rcwmask) -i 1))) 0))
  let rcwsoftmask ← (( do
    if (((Sail.BitVec.length rcwsoftmask) == 64) : Bool)
    then
      (do
        let rcwsoftmask : (BitVec k_N) :=
          (Sail.BitVec.updateSubrange rcwsoftmask 49 18
            (BitVec.replicateBits
              (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rcwsoftmask 17)])) 32))
        let rcwsoftmask : (BitVec k_N) := (BitVec.update rcwsoftmask 0 (Bit 0#1))
        let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
        let w__3 ← (( do (ProtectionEnabled w__2.EL) ) : SailM Bool )
        let rcwsoftmask : (BitVec k_N) :=
          if (w__3 : Bool)
          then (BitVec.update rcwsoftmask 52 (Bit 0#1))
          else rcwsoftmask
        (pure (rcwsoftmask)))
    else
      (let rcwsoftmask : (BitVec k_N) :=
        (Sail.BitVec.updateSubrange rcwsoftmask 55 17
          (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rcwsoftmask 16)]))
            39))
      let split_vec := (Zeros (n := 48))
      let rcwsoftmask : (BitVec k_N) :=
        (Sail.BitVec.updateSubrange rcwsoftmask 126 125 (Sail.BitVec.extractLsb split_vec 47 46))
      let rcwsoftmask : (BitVec k_N) :=
        (Sail.BitVec.updateSubrange rcwsoftmask 120 119 (Sail.BitVec.extractLsb split_vec 45 44))
      let rcwsoftmask : (BitVec k_N) :=
        (Sail.BitVec.updateSubrange rcwsoftmask 107 101 (Sail.BitVec.extractLsb split_vec 43 37))
      let rcwsoftmask : (BitVec k_N) :=
        (Sail.BitVec.updateSubrange rcwsoftmask 90 56 (Sail.BitVec.extractLsb split_vec 36 2))
      let rcwsoftmask : (BitVec k_N) :=
        (Sail.BitVec.updateSubrange rcwsoftmask 1 0 (Sail.BitVec.extractLsb split_vec 1 0))
      let rcwsoftmask : (BitVec k_N) := (BitVec.update rcwsoftmask 114 (Bit 0#1))
      (pure (rcwsoftmask))) ) : SailM (BitVec k_N) )
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__5 ← (( do (ProtectionEnabled w__4.EL) ) : SailM Bool )
  let rcw_state_fail ← (( do
    if (w__5 : Bool)
    then
      (do
        ArmFull.assert ((0 ≤b protectedbit) && (protectedbit <b (Sail.BitVec.length rcwsoftmask))) "sail-inputs/03-v8_base.sail:28550.68-28550.69"
        let rcw_state_fail : Bool :=
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access old protectedbit)])) == 1#1) : Bool)
          then
            (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access new protectedbit)])) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                    new 0)]))) != ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access old protectedbit)])) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                    old 0)]))))
          else
            (if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access old protectedbit)])) == 0#1) : Bool)
            then
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access new protectedbit)])) != (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                    old protectedbit)])))
            else rcw_state_fail)
        (pure (rcw_state_fail)))
    else (pure (rcw_state_fail)) ) : SailM Bool )
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__7 ← (( do (ProtectionEnabled w__6.EL) ) : SailM Bool )
  let rcw_mask_fail ← (( do
    if (w__7 : Bool)
    then
      (do
        ArmFull.assert ((0 ≤b protectedbit) && (protectedbit <b (Sail.BitVec.length rcwsoftmask))) "sail-inputs/03-v8_base.sail:28558.68-28558.69"
        let rcw_mask_fail : Bool :=
          if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access old protectedbit)])) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     old 0)]))) == 0b11#2) : Bool)
          then (! (IsZero ((new ^^^ old) &&& (Complement.complement rcwmask))))
          else rcw_mask_fail
        (pure (rcw_mask_fail)))
    else (pure (rcw_mask_fail)) ) : SailM Bool )
  let (rcws_mask_fail, rcws_state_fail) ← (( do
    if (soft : Bool)
    then
      (do
        let rcws_state_fail ← (( do
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access old 0)])) == 1#1) : Bool)
          then
            (let rcws_state_fail : Bool :=
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access new 0)])) != (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                    old 0)])))
            (pure (rcws_state_fail)))
          else
            (do
              ArmFull.assert ((0 ≤b protectedbit) && (protectedbit <b (Sail.BitVec.length
                    rcwsoftmask))) "sail-inputs/03-v8_base.sail:28568.72-28568.73"
              let w__13 ← (( do
                if ((← do
                     let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
                     let w__9 ← (( do (ProtectionEnabled w__8.EL) ) : SailM Bool )
                     (pure (((! w__9) : Bool)))) : Bool)
                then (pure true)
                else
                  (do
                    (pure ((← do
                          let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
                          (ProtectionEnabled w__10.EL)) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                              old protectedbit)])) == 0#1) : Bool)))) ) : SailM Bool )
              let rcws_state_fail : Bool :=
                if (w__13 : Bool)
                then
                  ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access new 0)])) != (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                        old 0)])))
                else rcws_state_fail
              (pure (rcws_state_fail))) ) : SailM Bool )
        let rcws_mask_fail : Bool :=
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access old 0)])) == 1#1) : Bool)
          then (! (IsZero ((new ^^^ old) &&& (Complement.complement rcwsoftmask))))
          else rcws_mask_fail
        (pure ((rcws_mask_fail, rcws_state_fail))))
    else (pure ((rcws_mask_fail, rcws_state_fail))) ) : SailM (Bool × Bool) )
  let rcw_fail : Bool := (rcw_state_fail || rcw_mask_fail)
  let rcws_fail : Bool := (rcws_state_fail || rcws_mask_fail)
  let n : (BitVec 1) := 0#1
  let z : (BitVec 1) :=
    if (rcw_fail : Bool)
    then 1#1
    else 0#1
  let c : (BitVec 1) :=
    if (rcws_fail : Bool)
    then 0#1
    else 1#1
  let v : (BitVec 1) := 0#1
  (pure ((((n +++ z) +++ c) +++ v)))


def AArch64_AddressWithAllocationTag (address : (BitVec 64)) (allocation_tag : (BitVec 4)) : SailM (BitVec 64) := do
  let result : (BitVec 64) := address
  let tag ← (( do (undefined_bitvector_at (← occLabel 1664) 4) ) : SailM (BitVec 4) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (AArch64_AllocationTagAccessIsEnabled w__0.EL) ) : SailM Bool )
  let tag : (BitVec 4) :=
    if (w__1 : Bool)
    then allocation_tag
    else 0b0000#4
  let result : (BitVec 64) := (Sail.BitVec.updateSubrange result 59 56 tag)
  (pure (result))


/-- Type quantifiers: n : Int, width : Nat, width ≥ 0 -/
def Z_read (n : Int) (width : Nat) : SailM (BitVec width) := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  ArmFull.assert ((n ≥b 0) && (n ≤b 31)) "sail-inputs/03-v8_base.sail:29656.27-29656.28"
  ArmFull.assert (width == VL) "sail-inputs/03-v8_base.sail:29657.22-29657.23"
  let w__0 ← (( do readReg _Z ) : SailM (Vector (BitVec 2048) 32) )
  (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb
      (GetElem?.getElem! w__0 (Sail.Int.toNatChecked (n))) (Sail.Int.toNatChecked ((width -i 1))) 0))))


/-- Type quantifiers: n : Int, width : Nat, width ≥ 0 ∧
  (Sail.Int.toNatChecked (n : Int)) < 16 ∨
  (not ((Sail.Int.toNatChecked (n : Int)) ≥ 0 ∧ (Sail.Int.toNatChecked (n : Int)) ≤ 31)) -/
def P_read (n : Int) (width : Nat) : SailM (BitVec width) := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  ArmFull.assert ((n ≥b 0) && (n ≤b 31)) "sail-inputs/03-v8_base.sail:29667.27-29667.28"
  ArmFull.assert (width == (Int.ediv (Sail.Int.toNatChecked (VL)) 8)) "sail-inputs/03-v8_base.sail:29668.30-29668.31"
  let w__0 ← (( do readReg _P ) : SailM (Vector (BitVec 256) 16) )
  (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb
      (GetElem?.getElem! w__0 (Sail.Int.toNatChecked (n))) (Sail.Int.toNatChecked ((width -i 1))) 0))))


/-- Type quantifiers: width : Nat, width ≥ 0 -/
def FFR_read (width : Nat) : SailM (BitVec width) := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  ArmFull.assert (width == (Int.ediv (Sail.Int.toNatChecked (VL)) 8)) "sail-inputs/03-v8_base.sail:29676.30-29676.31"
  let w__0 ← (( do readReg _FFR ) : SailM (BitVec 256) )
  (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__0 (Sail.Int.toNatChecked ((width -i 1)))
      0))))


/-- Type quantifiers: e : Int, esize : Int -/
def ElemFFR_set (e : Int) (esize : Int) (value_name : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let psize : Int := (fdiv_int esize 8)
  let n : Int := (e *i psize)
  ArmFull.assert ((n ≥b 0) && ((n +i psize) ≤b (Int.ediv (Sail.Int.toNatChecked (VL)) 8))) "sail-inputs/03-v8_base.sail:29846.43-29846.44"
  ArmFull.assert (n ≤b ((n +i psize) -i 1)) "sail-inputs/03-v8_base.sail:29847.44-29847.45"
  let w__0 ← (( do readReg _FFR ) : SailM (BitVec 256) )
  writeReg _FFR (Sail.BitVec.castWidth (m := 256) (Sail.BitVec.updateSubrange w__0
    (Sail.Int.toNatChecked (((n +i psize) -i 1))) (Sail.Int.toNatChecked (n))
    (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend value_name (Sail.Int.toNatChecked (psize))))))


/-- Type quantifiers: esize : Int -/
def DecodePredCount (pattern : (BitVec 5)) (esize : Int) : SailM Int := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let elements : Int := (fdiv_int VL esize)
  let numElem ← (( do (undefined_int_at (← occLabel 1743) ()) ) : SailM Int )
  let numElem ← (( do
    match pattern with
    | 0b00000 =>
      (do
        (FloorPow2 elements))
    | 0b00001 =>
      (let numElem : Int :=
        if ((elements ≥b 1) : Bool)
        then 1
        else 0
      (pure (numElem)))
    | 0b00010 =>
      (let numElem : Int :=
        if ((elements ≥b 2) : Bool)
        then 2
        else 0
      (pure (numElem)))
    | 0b00011 =>
      (let numElem : Int :=
        if ((elements ≥b 3) : Bool)
        then 3
        else 0
      (pure (numElem)))
    | 0b00100 =>
      (let numElem : Int :=
        if ((elements ≥b 4) : Bool)
        then 4
        else 0
      (pure (numElem)))
    | 0b00101 =>
      (let numElem : Int :=
        if ((elements ≥b 5) : Bool)
        then 5
        else 0
      (pure (numElem)))
    | 0b00110 =>
      (let numElem : Int :=
        if ((elements ≥b 6) : Bool)
        then 6
        else 0
      (pure (numElem)))
    | 0b00111 =>
      (let numElem : Int :=
        if ((elements ≥b 7) : Bool)
        then 7
        else 0
      (pure (numElem)))
    | 0b01000 =>
      (let numElem : Int :=
        if ((elements ≥b 8) : Bool)
        then 8
        else 0
      (pure (numElem)))
    | 0b01001 =>
      (let numElem : Int :=
        if ((elements ≥b 16) : Bool)
        then 16
        else 0
      (pure (numElem)))
    | 0b01010 =>
      (let numElem : Int :=
        if ((elements ≥b 32) : Bool)
        then 32
        else 0
      (pure (numElem)))
    | 0b01011 =>
      (let numElem : Int :=
        if ((elements ≥b 64) : Bool)
        then 64
        else 0
      (pure (numElem)))
    | 0b01100 =>
      (let numElem : Int :=
        if ((elements ≥b 128) : Bool)
        then 128
        else 0
      (pure (numElem)))
    | 0b01101 =>
      (let numElem : Int :=
        if ((elements ≥b 256) : Bool)
        then 256
        else 0
      (pure (numElem)))
    | 0b11101 =>
      (let numElem : Int := (elements -i (fmod_int elements 4))
      (pure (numElem)))
    | 0b11110 =>
      (let numElem : Int := (elements -i (fmod_int elements 3))
      (pure (numElem)))
    | 0b11111 => (pure (elements))
    | _ => (pure (0)) ) : SailM Int )
  let numElem : Int := numElem
  (pure (numElem))


/-- Type quantifiers: esize : Int, slice_name : Int, tile : Int, width : Nat, width ≥ 0 -/
def ZAhslice_read (tile : Int) (esize : Int) (slice_name : Int) (width : Nat) : SailM (BitVec width) := do
  let SVL ← (( do (CurrentSVL_read ()) ) : SailM Int )
  ArmFull.assert ((esize == 8) || ((esize == 16) || ((esize == 32) || ((esize == 64) || (esize == 128))))) "sail-inputs/03-v8_base.sail:31169.78-31169.79"
  let tiles : Int := (Int.ediv (Sail.Int.toNatChecked (esize)) 8)
  ArmFull.assert ((tile ≥b 0) && (tile <b tiles)) "sail-inputs/03-v8_base.sail:31171.35-31171.36"
  let slices : Int := (Int.ediv (Sail.Int.toNatChecked (SVL)) (Sail.Int.toNatChecked (esize)))
  ArmFull.assert ((slice_name ≥b 0) && (slice_name <b slices)) "sail-inputs/03-v8_base.sail:31173.48-31173.49"
  ((Sail.BitVec.castWidth ) <$> (ZAvector_read (tile +i (slice_name *i tiles)) width))


/-- Type quantifiers: esize : Int, slice_name : Int, tile : Int, width : Nat, width ≥ 0 -/
def ZAhslice_set (tile : Int) (esize : Int) (slice_name : Int) (width : Nat) (value_name : (BitVec width)) : SailM Unit := do
  let SVL ← (( do (CurrentSVL_read ()) ) : SailM Int )
  ArmFull.assert ((esize == 8) || ((esize == 16) || ((esize == 32) || ((esize == 64) || (esize == 128))))) "sail-inputs/03-v8_base.sail:31183.78-31183.79"
  let tiles : Int := (Int.ediv (Sail.Int.toNatChecked (esize)) 8)
  ArmFull.assert ((tile ≥b 0) && (tile <b tiles)) "sail-inputs/03-v8_base.sail:31185.35-31185.36"
  let slices : Int := (Int.ediv (Sail.Int.toNatChecked (SVL)) (Sail.Int.toNatChecked (esize)))
  ArmFull.assert ((slice_name ≥b 0) && (slice_name <b slices)) "sail-inputs/03-v8_base.sail:31187.48-31187.49"
  (ZAvector_set (tile +i (slice_name *i tiles)) width (Sail.BitVec.castWidth value_name))


/-- Type quantifiers: width : Nat, width ≥ 0 -/
def CounterToPredicate (pred : (BitVec 16)) (width : Nat) : SailM (BitVec width) := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let count ← (( do (undefined_int_at (← occLabel 1754) ()) ) : SailM Int )
  let esize : Int := 8
  let VL : Int := VL
  let PL : Int := (Int.ediv (Sail.Int.toNatChecked (VL)) 8)
  let w__0 ← (( do (CeilPow2 (PL *i 4)) ) : SailM Nat )
  let maxbit : Int := (HighestSetBit (integer_subrange w__0 15 0))
  ArmFull.assert (maxbit ≤b 14) "sail-inputs/03-v8_base.sail:31329.23-31329.24"
  let invert : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access pred 15)])) == 1#1)
  ArmFull.assert ((((width == PL) || (width == (PL *i 2))) || (width == (PL *i 3))) || (width == (PL *i 4))) "sail-inputs/03-v8_base.sail:31331.80-31331.81"
  if ((IsZero (Sail.BitVec.extractLsb pred 3 0)) : Bool)
  then (pure ((Sail.BitVec.castWidth (Zeros (n := width)))))
  else
    (do
      let b__0 := (Sail.BitVec.extractLsb pred 3 0)
      let (count, esize) ← (( do
        if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (1#1 : (BitVec 1))) : Bool)
        then
          (do
            ArmFull.assert ((1 ≤b maxbit) && (maxbit <b 16)) "sail-inputs/03-v8_base.sail:31337.58-31337.59"
            let count : Int :=
              (BitVec.toNat (Sail.BitVec.extractLsb pred (Sail.Int.toNatChecked (maxbit)) 1))
            let esize : Int := 8
            (pure ((count, esize))))
        else
          (do
            if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 1 0)) == (0b10#2 : (BitVec 2))) : Bool)
            then
              (do
                ArmFull.assert ((2 ≤b maxbit) && (maxbit <b 16)) "sail-inputs/03-v8_base.sail:31342.58-31342.59"
                let count : Int :=
                  (BitVec.toNat (Sail.BitVec.extractLsb pred (Sail.Int.toNatChecked (maxbit)) 2))
                let esize : Int := 16
                (pure ((count, esize))))
            else
              (do
                if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 2 0)) == (0b100#3 : (BitVec 3))) : Bool)
                then
                  (do
                    ArmFull.assert ((3 ≤b maxbit) && (maxbit <b 16)) "sail-inputs/03-v8_base.sail:31347.58-31347.59"
                    let count : Int :=
                      (BitVec.toNat (Sail.BitVec.extractLsb pred (Sail.Int.toNatChecked (maxbit)) 3))
                    let esize : Int := 32
                    (pure ((count, esize))))
                else
                  (do
                    match b__0 with
                    | 0b1000 =>
                      (do
                        ArmFull.assert ((4 ≤b maxbit) && (maxbit <b 16)) "sail-inputs/03-v8_base.sail:31352.58-31352.59"
                        let count : Int :=
                          (BitVec.toNat
                            (Sail.BitVec.extractLsb pred (Sail.Int.toNatChecked (maxbit)) 4))
                        let esize : Int := 64
                        (pure ((count, esize))))
                    | _ => (pure ((count, esize)))))) ) : SailM (Int × Int) )
      let esize : Int := esize
      let count : Int := count
      let elements : Int :=
        (Int.ediv (Sail.Int.toNatChecked ((VL *i 4))) (Sail.Int.toNatChecked (esize)))
      let result : (BitVec (Sail.Int.toNatChecked ((PL : Int) *i (4 : Int)))) :=
        (Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked ((PL *i 4))))))
      let psize : Int := (Int.ediv (Sail.Int.toNatChecked (esize)) 8)
      let result ← (( do
        let loop_e_lower : Nat := 0
        let loop_e_upper : Int := (elements -i 1)
        (do
          let mut loop_vars := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars
            loop_vars ← do
              let pbit : (BitVec 1) :=
                if ((e <b count) : Bool)
                then 1#1
                else 0#1
              let pbit : (BitVec 1) :=
                if (invert : Bool)
                then (Complement.complement pbit)
                else pbit
              (Elem_set result e (Sail.Int.toNatChecked (psize))
                (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit (Sail.Int.toNatChecked (psize)))))
          (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked ((PL : Int) *i (4 : Int)))) )
      (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb result
          (Sail.Int.toNatChecked ((width -i 1))) 0)))))


/-- Type quantifiers: count_in : Int, elements : Int, esize : Int, k_invert_in : Bool, width : Nat, width
  ≥ 0 -/
def EncodePredCount (esize : Int) (elements : Int) (count_in : Int) (invert_in : Bool) (width : Nat) : SailM (BitVec width) := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let count : Int := count_in
  let invert : Bool := invert_in
  let PL : Int := (Int.ediv (Sail.Int.toNatChecked (VL)) 8)
  ArmFull.assert (width == PL) "sail-inputs/03-v8_base.sail:31382.22-31382.23"
  ArmFull.assert ((esize == 8) || ((esize == 16) || ((esize == 32) || (esize == 64)))) "sail-inputs/03-v8_base.sail:31383.63-31383.64"
  ArmFull.assert ((count ≥b 0) && (count ≤b elements)) "sail-inputs/03-v8_base.sail:31384.41-31384.42"
  let pred ← (( do (undefined_bitvector_at (← occLabel 1755) 16) ) : SailM (BitVec 16) )
  let w__0 : (BitVec width) :=
    if ((count == 0) : Bool)
    then (Sail.BitVec.castWidth (Zeros (n := width)))
    else
      (let (count, invert) : (Int × Bool) :=
        if (invert : Bool)
        then
          (let count : Int := (elements -i count)
          (count, invert))
        else
          (let (count, invert) : (Int × Bool) :=
            if ((count == elements) : Bool)
            then
              (let count : Int := 0
              let invert : Bool := true
              (count, invert))
            else (count, invert)
          (count, invert))
      let count : Int := count
      let inv : (BitVec 1) :=
        if (invert : Bool)
        then 1#1
        else 0#1
      let pred : (BitVec 16) :=
        match esize with
        | 8 => ((inv +++ (integer_subrange count 13 0)) +++ 1#1)
        | 16 => ((inv +++ (integer_subrange count 12 0)) +++ 0b10#2)
        | 32 => ((inv +++ (integer_subrange count 11 0)) +++ 0b100#3)
        | 64 => ((inv +++ (integer_subrange count 10 0)) +++ 0b1000#4)
        | _ => pred
      (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pred width)))
  (pure ((Sail.BitVec.castWidth w__0)))


def AArch64_ESBOperation (_ : Unit) : SailM Unit := do
  let implicit_esb ← (( do (undefined_bool_at (← occLabel 1930) ()) ) : SailM Bool )
  let target_el ← (( do (undefined_bitvector_at (← occLabel 1931) 2) ) : SailM (BitVec 2) )
  let masked ← (( do (undefined_bool_at (← occLabel 1932) ()) ) : SailM Bool )
  let w__0 ← (( do (AArch64_PhysicalSErrorTarget ()) ) : SailM (Bool × (BitVec 2)) )
  let (tup__0, tup__1) := (w__0 : (Bool × (BitVec 2)))
  let masked : Bool := tup__0
  let target_el : (BitVec 2) := tup__1
  let intdis ← (( do
    if ((← do
         (Halted ())) : Bool)
    then (pure true)
    else
      (do
        (ExternalDebugInterruptsDisabled target_el)) ) : SailM Bool )
  let masked : Bool := (masked || intdis)
  let w__4 ← (( do
    if (masked : Bool)
    then
      (do
        (IsSynchronizablePhysicalSErrorPending ()))
    else (pure false) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      let w__5 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
      let w__6 ← (( do (ELUsingAArch32 w__5) ) : SailM Bool )
      if (w__6 : Bool)
      then
        (do
          let syndrome : (BitVec 32) := (Zeros (n := 32))
          let syndrome : (BitVec 32) := (BitVec.update syndrome 31 (Bit 1#1))
          let w__7 ← (( do (AArch32_PhysicalSErrorSyndrome ()) ) : SailM (BitVec 16) )
          let syndrome := ((Sail.BitVec.updateSubrange syndrome 15 0 w__7) : (BitVec 32))
          (DISR_write (Mk_DISR_Type syndrome)))
      else
        (do
          let implicit_esb : Bool := false
          let syndrome : (BitVec 64) := (Zeros (n := 64))
          let syndrome : (BitVec 64) := (BitVec.update syndrome 31 (Bit 1#1))
          let w__8 ← (( do (AArch64_PhysicalSErrorSyndrome implicit_esb) ) : SailM (BitVec 25) )
          let syndrome := ((Sail.BitVec.updateSubrange syndrome 24 0 w__8) : (BitVec 64))
          writeReg DISR_EL1 (Mk_DISR_EL1_Type syndrome))
      (pure ((ClearPendingPhysicalSError ()))))
  else (pure (()))


/-- Type quantifiers: k_cold : Bool -/
def AArch32_AutoGen_ArchitectureReset (cold : Bool) : SailM Unit := do
  let split_c0 ← (( (AArch32_AutoGen_ArchitectureReset__seg0 cold) ) : SailM Bool )
  if (split_c0 : Bool)
  then
    (do
      let split_c1 ← (( (AArch32_AutoGen_ArchitectureReset__seg1 cold) ) : SailM Bool )
      if (split_c1 : Bool)
      then
        (do
          let split_c2 ← (( (AArch32_AutoGen_ArchitectureReset__seg2 cold) ) : SailM Bool )
          if (split_c2 : Bool)
          then (AArch32_AutoGen_ArchitectureReset__seg3 cold)
          else (pure ()))
      else (pure ()))
  else (pure ())


/-- Type quantifiers: k_cold : Bool -/
def AArch64_AutoGen_ArchitectureReset__seg5 (cold : Bool) : SailM Unit := do
  let w__1841 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1841 : Bool)
  then
    (do
      let w__1842 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1843 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1842 6 6 w__1843))
  else (pure (()))
  let w__1845 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1844 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1844) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1845 : Bool)
  then
    (do
      let w__1846 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1847 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1846 6 6 w__1847))
  else (pure (()))
  let w__1848 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
  writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1848 5 0 0b000000#6)
  let w__1849 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
  writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange w__1849 63 47 0b00000000000000000#17)
  let w__1850 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
  writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange w__1850 31 18 0b00000000000000#14)
  let w__1851 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
  writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange w__1851 15 14 0b00#2)
  let w__1852 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
  writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange w__1852 4 2 0b000#3)
  let w__1853 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1853 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__1855 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1855 : Bool)
  then
    (do
      let w__1856 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1857 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1856 23 23 w__1857))
  else (pure (()))
  let w__1859 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1858 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1858) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1859 : Bool)
  then
    (do
      let w__1860 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1861 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1860 23 23 w__1861))
  else (pure (()))
  let w__1863 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1863 : Bool)
  then
    (do
      let w__1864 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1865 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1864 22 22 w__1865))
  else (pure (()))
  let w__1867 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1866 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1866) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1867 : Bool)
  then
    (do
      let w__1868 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1869 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1868 22 22 w__1869))
  else (pure (()))
  let w__1870 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1870 21 10 0b000000000000#12)
  let w__1872 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1872 : Bool)
  then
    (do
      let w__1873 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1874 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1873 8 8 w__1874))
  else (pure (()))
  let w__1876 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1875 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1875) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1876 : Bool)
  then
    (do
      let w__1877 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1878 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1877 8 8 w__1878))
  else (pure (()))
  let w__1879 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL1 (BitVec.update w__1879 7 (Bit 0#1))
  let w__1881 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1881 : Bool)
  then
    (do
      let w__1882 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1883 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1882 6 5 w__1883))
  else (pure (()))
  let w__1885 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1884 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1884) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1885 : Bool)
  then
    (do
      let w__1886 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1887 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1886 6 5 w__1887))
  else (pure (()))
  let w__1889 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1889 : Bool)
  then
    (do
      let w__1890 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1891 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1890 4 4 w__1891))
  else (pure (()))
  let w__1893 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1892 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1892) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1893 : Bool)
  then
    (do
      let w__1894 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1895 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1894 4 4 w__1895))
  else (pure (()))
  let w__1897 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1897 : Bool)
  then
    (do
      let w__1898 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1899 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1898 3 3 w__1899))
  else (pure (()))
  let w__1901 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1900 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1900) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1901 : Bool)
  then
    (do
      let w__1902 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1903 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1902 3 3 w__1903))
  else (pure (()))
  let w__1904 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL1 (BitVec.update w__1904 2 (Bit 0#1))
  let w__1905 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1905 1 1 0#1)
  let w__1906 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1906 0 0 0#1)
  let w__1907 ← (( do readReg BRBIDR0_EL1 ) : SailM (BitVec 64) )
  writeReg BRBIDR0_EL1 (Sail.BitVec.updateSubrange w__1907 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__1908 ← (( do readReg GCSPR_EL3 ) : SailM (BitVec 64) )
  writeReg GCSPR_EL3 (Sail.BitVec.updateSubrange w__1908 2 0 0b000#3)
  let w__1909 ← (( do readReg GCSPR_EL1 ) : SailM (BitVec 64) )
  writeReg GCSPR_EL1 (Sail.BitVec.updateSubrange w__1909 2 0 0b000#3)
  let w__1910 ← (( do readReg GCSCR_EL3 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL3 (Sail.BitVec.updateSubrange w__1910 63 10
    0b000000000000000000000000000000000000000000000000000000#54)
  let w__1911 ← (( do readReg GCSCR_EL3 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL3 (Sail.BitVec.updateSubrange w__1911 9 9 0#1)
  let w__1912 ← (( do readReg GCSCR_EL3 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL3 (Sail.BitVec.updateSubrange w__1912 8 8 0#1)
  let w__1913 ← (( do readReg GCSCR_EL3 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL3 (BitVec.update w__1913 7 (Bit 0#1))
  let w__1914 ← (( do readReg GCSCR_EL3 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL3 (Sail.BitVec.updateSubrange w__1914 6 6 0#1)
  let w__1915 ← (( do readReg GCSCR_EL3 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL3 (Sail.BitVec.updateSubrange w__1915 4 1 0b0000#4)
  let w__1916 ← (( do readReg GCSCR_EL3 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL3 (Sail.BitVec.updateSubrange w__1916 0 0 0#1)
  let w__1917 ← (( do readReg GCSCR_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL1 (Sail.BitVec.updateSubrange w__1917 63 10
    0b000000000000000000000000000000000000000000000000000000#54)
  let w__1918 ← (( do readReg GCSCR_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL1 (Sail.BitVec.updateSubrange w__1918 9 9 0#1)
  let w__1919 ← (( do readReg GCSCR_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL1 (Sail.BitVec.updateSubrange w__1919 8 8 0#1)
  let w__1920 ← (( do readReg GCSCR_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL1 (BitVec.update w__1920 7 (Bit 0#1))
  let w__1921 ← (( do readReg GCSCR_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL1 (Sail.BitVec.updateSubrange w__1921 6 6 0#1)
  let w__1922 ← (( do readReg GCSCR_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL1 (Sail.BitVec.updateSubrange w__1922 4 1 0b0000#4)
  let w__1923 ← (( do readReg GCSCR_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL1 (Sail.BitVec.updateSubrange w__1923 0 0 0#1)
  let w__1924 ← (( do readReg GCSPR_EL2 ) : SailM (BitVec 64) )
  writeReg GCSPR_EL2 (Sail.BitVec.updateSubrange w__1924 2 0 0b000#3)
  let w__1925 ← (( do readReg GCSCR_EL2 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL2 (Sail.BitVec.updateSubrange w__1925 63 10
    0b000000000000000000000000000000000000000000000000000000#54)
  let w__1926 ← (( do readReg GCSCR_EL2 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL2 (Sail.BitVec.updateSubrange w__1926 9 9 0#1)
  let w__1927 ← (( do readReg GCSCR_EL2 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL2 (Sail.BitVec.updateSubrange w__1927 8 8 0#1)
  let w__1928 ← (( do readReg GCSCR_EL2 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL2 (BitVec.update w__1928 7 (Bit 0#1))
  let w__1929 ← (( do readReg GCSCR_EL2 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL2 (Sail.BitVec.updateSubrange w__1929 6 6 0#1)
  let w__1930 ← (( do readReg GCSCR_EL2 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL2 (Sail.BitVec.updateSubrange w__1930 4 1 0b0000#4)
  let w__1931 ← (( do readReg GCSCR_EL2 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL2 (Sail.BitVec.updateSubrange w__1931 0 0 0#1)
  let w__1932 ← (( do readReg GCSCRE0_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCRE0_EL1 (Sail.BitVec.updateSubrange w__1932 63 11
    0b00000000000000000000000000000000000000000000000000000#53)
  let w__1933 ← (( do readReg GCSCRE0_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCRE0_EL1 (Sail.BitVec.updateSubrange w__1933 10 10 0#1)
  let w__1934 ← (( do readReg GCSCRE0_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCRE0_EL1 (Sail.BitVec.updateSubrange w__1934 9 9 0#1)
  let w__1935 ← (( do readReg GCSCRE0_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCRE0_EL1 (Sail.BitVec.updateSubrange w__1935 8 8 0#1)
  let w__1936 ← (( do readReg GCSCRE0_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCRE0_EL1 (Sail.BitVec.updateSubrange w__1936 7 6 0b00#2)
  let w__1937 ← (( do readReg GCSCRE0_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCRE0_EL1 (Sail.BitVec.updateSubrange w__1937 4 1 0b0000#4)
  let w__1938 ← (( do readReg GCSCRE0_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCRE0_EL1 (Sail.BitVec.updateSubrange w__1938 0 0 0#1)
  let w__1939 ← (( do readReg GCSPR_EL0 ) : SailM (BitVec 64) )
  writeReg GCSPR_EL0 (Sail.BitVec.updateSubrange w__1939 2 0 0b000#3)
  let w__1940 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
  (PAR_EL1_write (Mk_PAR_EL1_Type (set_slice 8 w__1940 120 0b00000000#8)))
  let w__1941 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
  (PAR_EL1_write (Mk_PAR_EL1_Type (set_slice 11 w__1941 65 0b00000000000#11)))
  let w__1942 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
  (PAR_EL1_write
    (Mk_PAR_EL1_Type (set_slice 44 w__1942 12 0b00000000000000000000000000000000000000000000#44)))
  let w__1943 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
  (PAR_EL1_write (Mk_PAR_EL1_Type (set_slice 6 w__1943 1 0b000000#6)))
  let w__1944 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
  (PAR_EL1_write
    (Mk_PAR_EL1_Type
      (set_slice 63 w__1944 65 0b000000000000000000000000000000000000000000000000000000000000000#63)))
  let w__1945 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
  (PAR_EL1_write (Mk_PAR_EL1_Type (set_slice 32 w__1945 16 0b00000000000000000000000000000000#32)))
  let w__1946 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
  (PAR_EL1_write (Mk_PAR_EL1_Type (set_slice 1 w__1946 11 1#1)))
  let w__1947 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
  (PAR_EL1_write (Mk_PAR_EL1_Type (set_slice 1 w__1947 10 0#1)))
  let w__1948 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
  (PAR_EL1_write (Mk_PAR_EL1_Type (set_slice 1 w__1948 7 0#1)))
  let w__1949 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
  (PAR_EL1_write
    (Mk_PAR_EL1_Type
      (set_slice 63 w__1949 65 0b000000000000000000000000000000000000000000000000000000000000000#63)))
  let w__1950 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
  (PAR_EL1_write (Mk_PAR_EL1_Type (set_slice 4 w__1950 52 0b0000#4)))
  let w__1951 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
  (PAR_EL1_write (Mk_PAR_EL1_Type (set_slice 6 w__1951 1 0b000000#6)))
  let w__1952 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
  (PAR_EL1_write
    (Mk_PAR_EL1_Type
      (set_slice 63 w__1952 65 0b000000000000000000000000000000000000000000000000000000000000000#63)))
  let w__1953 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
  (PAR_EL1_write (Mk_PAR_EL1_Type (set_slice 32 w__1953 16 0b00000000000000000000000000000000#32)))
  let w__1954 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
  (PAR_EL1_write (Mk_PAR_EL1_Type (set_slice 1 w__1954 11 1#1)))
  let w__1955 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
  (PAR_EL1_write (Mk_PAR_EL1_Type (set_slice 1 w__1955 10 0#1)))
  let w__1956 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
  (PAR_EL1_write (Mk_PAR_EL1_Type (set_slice 1 w__1956 7 0#1)))
  let w__1957 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
  (PAR_EL1_write (Mk_PAR_EL1_Type (set_slice 4 w__1957 52 0b0000#4)))
  let w__1958 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
  (PAR_EL1_write (Mk_PAR_EL1_Type (set_slice 6 w__1958 1 0b000000#6)))
  let w__1959 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
  (PAR_EL1_write (Mk_PAR_EL1_Type (set_slice 32 w__1959 16 0b00000000000000000000000000000000#32)))
  let w__1960 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
  (PAR_EL1_write (Mk_PAR_EL1_Type (set_slice 1 w__1960 11 1#1)))
  let w__1961 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
  (PAR_EL1_write (Mk_PAR_EL1_Type (set_slice 1 w__1961 10 0#1)))
  let w__1962 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
  (PAR_EL1_write (Mk_PAR_EL1_Type (set_slice 1 w__1962 7 0#1)))
  let w__1963 ← (( do (TTBR1_EL1_read ()) ) : SailM (BitVec 128) )
  (TTBR1_EL1_write
    (Mk_TTBR1_EL1_Type (set_slice 40 w__1963 88 0b0000000000000000000000000000000000000000#40)))
  let w__1964 ← (( do (TTBR1_EL1_read ()) ) : SailM (BitVec 128) )
  (TTBR1_EL1_write (Mk_TTBR1_EL1_Type (set_slice 16 w__1964 64 0b0000000000000000#16)))
  let w__1965 ← (( do (TTBR1_EL1_read ()) ) : SailM (BitVec 128) )
  (TTBR1_EL1_write (Mk_TTBR1_EL1_Type (set_slice 2 w__1965 3 0b00#2)))
  let w__1966 ← (( do (TTBR0_EL2_read ()) ) : SailM (BitVec 128) )
  (TTBR0_EL2_write
    (Mk_TTBR0_EL2_Type (set_slice 40 w__1966 88 0b0000000000000000000000000000000000000000#40)))
  let w__1967 ← (( do (TTBR0_EL2_read ()) ) : SailM (BitVec 128) )
  (TTBR0_EL2_write (Mk_TTBR0_EL2_Type (set_slice 16 w__1967 64 0b0000000000000000#16)))
  let w__1968 ← (( do (TTBR0_EL2_read ()) ) : SailM (BitVec 128) )
  (TTBR0_EL2_write (Mk_TTBR0_EL2_Type (set_slice 2 w__1968 3 0b00#2)))
  let w__1969 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
  (VTTBR_EL2_write
    (Mk_VTTBR_EL2_Type (set_slice 40 w__1969 88 0b0000000000000000000000000000000000000000#40)))
  let w__1970 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
  (VTTBR_EL2_write (Mk_VTTBR_EL2_Type (set_slice 16 w__1970 64 0b0000000000000000#16)))
  let w__1971 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
  (VTTBR_EL2_write (Mk_VTTBR_EL2_Type (set_slice 2 w__1971 3 0b00#2)))
  let w__1972 ← (( do (TTBR0_EL1_read ()) ) : SailM (BitVec 128) )
  (TTBR0_EL1_write
    (Mk_TTBR0_EL1_Type (set_slice 40 w__1972 88 0b0000000000000000000000000000000000000000#40)))
  let w__1973 ← (( do (TTBR0_EL1_read ()) ) : SailM (BitVec 128) )
  (TTBR0_EL1_write (Mk_TTBR0_EL1_Type (set_slice 16 w__1973 64 0b0000000000000000#16)))
  let w__1974 ← (( do (TTBR0_EL1_read ()) ) : SailM (BitVec 128) )
  (TTBR0_EL1_write (Mk_TTBR0_EL1_Type (set_slice 2 w__1974 3 0b00#2)))
  let w__1975 ← (( do readReg TTBR1_EL2 ) : SailM (BitVec 128) )
  writeReg TTBR1_EL2 (Sail.BitVec.updateSubrange w__1975 127 88
    0b0000000000000000000000000000000000000000#40)
  let w__1976 ← (( do readReg TTBR1_EL2 ) : SailM (BitVec 128) )
  writeReg TTBR1_EL2 (Sail.BitVec.updateSubrange w__1976 79 64 0b0000000000000000#16)
  let w__1977 ← (( do readReg TTBR1_EL2 ) : SailM (BitVec 128) )
  writeReg TTBR1_EL2 (Sail.BitVec.updateSubrange w__1977 4 3 0b00#2)


end ArmFull.Functions
