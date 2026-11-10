import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0051
import ArmFull.Fn.M0061
import ArmFull.Fn.M0118
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0218
import ArmFull.Fn.M0852
import ArmFull.Fn.M0894
import ArmFull.Fn.M0895

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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, m : Nat, n : Nat, offs_size : Nat, k_offs_unsigned
  : Bool, scale : Nat, k_stream : Bool, scale = 2 ∧
  offs_size = 32 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem level [0, 1, 2, 3] ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_PRFW_I_P_BZ_S_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (m : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do (undefined_bitvector_at (← occLabel 5797) 64) ) : SailM (BitVec 64) )
  let offset ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5798)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__3 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let base := (w__3 : (BitVec 64))
        let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
        let offset := (w__4 : (BitVec VL))
        (pure ((base, offset))))
    else (pure ((base, offset))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let offset := offset
  let base := base
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__5 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__5 : Bool)
        then
          (do
            let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read offset e esize)) ) : SailM
              (BitVec esize) )
            let off ← (( do
              (asl_Int (Sail.BitVec.extractLsb w__6 (Sail.Int.toNatChecked ((offs_size -i 1))) 0)
                offs_unsigned) ) : SailM Int )
            let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
            (pure ((Hint_Prefetch addr pref_hint level stream))))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, m : Nat, n : Nat, offs_size : Nat, k_offs_unsigned
  : Bool, scale : Nat, k_stream : Bool, scale = 3 ∧
  offs_size = 32 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem level [0, 1, 2, 3] ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_PRFD_I_P_BZ_S_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (m : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do (undefined_bitvector_at (← occLabel 5799) 64) ) : SailM (BitVec 64) )
  let offset ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5800)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__3 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let base := (w__3 : (BitVec 64))
        let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
        let offset := (w__4 : (BitVec VL))
        (pure ((base, offset))))
    else (pure ((base, offset))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let offset := offset
  let base := base
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__5 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__5 : Bool)
        then
          (do
            let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read offset e esize)) ) : SailM
              (BitVec esize) )
            let off ← (( do
              (asl_Int (Sail.BitVec.extractLsb w__6 (Sail.Int.toNatChecked ((offs_size -i 1))) 0)
                offs_unsigned) ) : SailM Int )
            let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
            (pure ((Hint_Prefetch addr pref_hint level stream))))
        else (pure (()))
    (pure loop_vars))


def decode_PRFB_I_P_BI_S (imm6 : (BitVec 6)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 8
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Rn)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale : Nat := 0
  let offset : Int := (BitVec.toInt imm6)
  match VL with
  | 128 =>
    (do
      (execute_PRFB_I_P_BI_S 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) offset pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFB_I_P_BI_S 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) offset pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFB_I_P_BI_S 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) offset pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFB_I_P_BI_S 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) offset pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFB_I_P_BI_S 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) offset pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFH_I_P_BI_S (imm6 : (BitVec 6)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Rn)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale : Nat := 1
  let offset : Int := (BitVec.toInt imm6)
  match VL with
  | 128 =>
    (do
      (execute_PRFH_I_P_BI_S 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) offset pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFH_I_P_BI_S 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) offset pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFH_I_P_BI_S 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) offset pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFH_I_P_BI_S 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) offset pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFH_I_P_BI_S 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) offset pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFW_I_P_BI_S (imm6 : (BitVec 6)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Rn)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale : Nat := 2
  let offset : Int := (BitVec.toInt imm6)
  match VL with
  | 128 =>
    (do
      (execute_PRFW_I_P_BI_S 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) offset pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFW_I_P_BI_S 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) offset pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFW_I_P_BI_S 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) offset pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFW_I_P_BI_S 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) offset pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFW_I_P_BI_S 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) offset pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFD_I_P_BI_S (imm6 : (BitVec 6)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Rn)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale : Nat := 3
  let offset : Int := (BitVec.toInt imm6)
  match VL with
  | 128 =>
    (do
      (execute_PRFD_I_P_BI_S 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) offset pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFD_I_P_BI_S 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) offset pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFD_I_P_BI_S 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) offset pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFD_I_P_BI_S 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) offset pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFD_I_P_BI_S 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) offset pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFB_I_P_BR_S (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((Rm == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 8
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale : Nat := 0
  match VL with
  | 128 =>
    (do
      (execute_PRFB_I_P_BR_S 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFB_I_P_BR_S 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFB_I_P_BR_S 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFB_I_P_BR_S 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFB_I_P_BR_S 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFH_I_P_BR_S (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((Rm == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_PRFH_I_P_BR_S 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFH_I_P_BR_S 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFH_I_P_BR_S 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFH_I_P_BR_S 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFH_I_P_BR_S 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFW_I_P_BR_S (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((Rm == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_PRFW_I_P_BR_S 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFW_I_P_BR_S 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFW_I_P_BR_S 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFW_I_P_BR_S 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFW_I_P_BR_S 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFD_I_P_BR_S (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((Rm == 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale : Nat := 3
  match VL with
  | 128 =>
    (do
      (execute_PRFD_I_P_BR_S 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFD_I_P_BR_S 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFD_I_P_BR_S 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFD_I_P_BR_S 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFD_I_P_BR_S 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) pref_hint scale stream))
  | _ => (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, n : Nat, offset : Nat, scale :
  Nat, k_stream : Bool, scale = 0 ∧
  0 ≤ offset ∧
  offset ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem level [0, 1, 2, 3] ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_PRFB_I_P_AI_S (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (n : Nat) (offset : Nat) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5841)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure (base)) ) : SailM (BitVec VL) )
  let base := base
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__2 : Bool)
        then
          (do
            let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
              (BitVec esize) )
            let addr : (BitVec 64) :=
              (BitVec.addInt (Sail.BitVec.zeroExtend w__3 64) (Int.shiftl offset scale))
            (pure ((Hint_Prefetch addr pref_hint level stream))))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, n : Nat, offset : Nat, scale :
  Nat, k_stream : Bool, scale = 1 ∧
  0 ≤ offset ∧
  offset ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem level [0, 1, 2, 3] ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_PRFH_I_P_AI_S (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (n : Nat) (offset : Nat) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5842)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure (base)) ) : SailM (BitVec VL) )
  let base := base
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__2 : Bool)
        then
          (do
            let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
              (BitVec esize) )
            let addr : (BitVec 64) :=
              (BitVec.addInt (Sail.BitVec.zeroExtend w__3 64) (Int.shiftl offset scale))
            (pure ((Hint_Prefetch addr pref_hint level stream))))
        else (pure (()))
    (pure loop_vars))


end ArmFull.Functions
