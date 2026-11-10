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
import ArmFull.Fn.M0895
import ArmFull.Fn.M0896

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
  offs_size = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem level [0, 1, 2, 3] ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_PRFW_I_P_BZ_D_64_scaled (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (m : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do (undefined_bitvector_at (← occLabel 6506) 64) ) : SailM (BitVec 64) )
  let offset ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6507)
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
  offs_size = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem level [0, 1, 2, 3] ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_PRFD_I_P_BZ_D_64_scaled (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (m : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do (undefined_bitvector_at (← occLabel 6508) 64) ) : SailM (BitVec 64) )
  let offset ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6509)
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


def decode_SMOPA_ZA_PP_ZZ_32 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  let op1_unsigned : Bool := false
  let op2_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SMOPA_ZA_PP_ZZ_32 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 256 =>
    (do
      (execute_SMOPA_ZA_PP_ZZ_32 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 512 =>
    (do
      (execute_SMOPA_ZA_PP_ZZ_32 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 1024 =>
    (do
      (execute_SMOPA_ZA_PP_ZZ_32 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 2048 =>
    (do
      (execute_SMOPA_ZA_PP_ZZ_32 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | _ => (pure (()))


def decode_SUMOPA_ZA_PP_ZZ_32 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  let op1_unsigned : Bool := false
  let op2_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_SUMOPA_ZA_PP_ZZ_32 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 256 =>
    (do
      (execute_SUMOPA_ZA_PP_ZZ_32 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 512 =>
    (do
      (execute_SUMOPA_ZA_PP_ZZ_32 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 1024 =>
    (do
      (execute_SUMOPA_ZA_PP_ZZ_32 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 2048 =>
    (do
      (execute_SUMOPA_ZA_PP_ZZ_32 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | _ => (pure (()))


def decode_USMOPA_ZA_PP_ZZ_32 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  let op1_unsigned : Bool := true
  let op2_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_USMOPA_ZA_PP_ZZ_32 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 256 =>
    (do
      (execute_USMOPA_ZA_PP_ZZ_32 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 512 =>
    (do
      (execute_USMOPA_ZA_PP_ZZ_32 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 1024 =>
    (do
      (execute_USMOPA_ZA_PP_ZZ_32 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 2048 =>
    (do
      (execute_USMOPA_ZA_PP_ZZ_32 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | _ => (pure (()))


def decode_UMOPA_ZA_PP_ZZ_32 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  let op1_unsigned : Bool := true
  let op2_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_UMOPA_ZA_PP_ZZ_32 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 256 =>
    (do
      (execute_UMOPA_ZA_PP_ZZ_32 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 512 =>
    (do
      (execute_UMOPA_ZA_PP_ZZ_32 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 1024 =>
    (do
      (execute_UMOPA_ZA_PP_ZZ_32 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 2048 =>
    (do
      (execute_UMOPA_ZA_PP_ZZ_32 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | _ => (pure (()))


def decode_SMOPS_ZA_PP_ZZ_32 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  let op1_unsigned : Bool := false
  let op2_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SMOPS_ZA_PP_ZZ_32 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 256 =>
    (do
      (execute_SMOPS_ZA_PP_ZZ_32 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 512 =>
    (do
      (execute_SMOPS_ZA_PP_ZZ_32 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 1024 =>
    (do
      (execute_SMOPS_ZA_PP_ZZ_32 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 2048 =>
    (do
      (execute_SMOPS_ZA_PP_ZZ_32 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | _ => (pure (()))


def decode_SUMOPS_ZA_PP_ZZ_32 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  let op1_unsigned : Bool := false
  let op2_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_SUMOPS_ZA_PP_ZZ_32 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 256 =>
    (do
      (execute_SUMOPS_ZA_PP_ZZ_32 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 512 =>
    (do
      (execute_SUMOPS_ZA_PP_ZZ_32 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 1024 =>
    (do
      (execute_SUMOPS_ZA_PP_ZZ_32 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 2048 =>
    (do
      (execute_SUMOPS_ZA_PP_ZZ_32 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | _ => (pure (()))


def decode_USMOPS_ZA_PP_ZZ_32 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  let op1_unsigned : Bool := true
  let op2_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_USMOPS_ZA_PP_ZZ_32 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 256 =>
    (do
      (execute_USMOPS_ZA_PP_ZZ_32 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 512 =>
    (do
      (execute_USMOPS_ZA_PP_ZZ_32 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 1024 =>
    (do
      (execute_USMOPS_ZA_PP_ZZ_32 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 2048 =>
    (do
      (execute_USMOPS_ZA_PP_ZZ_32 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | _ => (pure (()))


def decode_UMOPS_ZA_PP_ZZ_32 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  let op1_unsigned : Bool := true
  let op2_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_UMOPS_ZA_PP_ZZ_32 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 256 =>
    (do
      (execute_UMOPS_ZA_PP_ZZ_32 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 512 =>
    (do
      (execute_UMOPS_ZA_PP_ZZ_32 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 1024 =>
    (do
      (execute_UMOPS_ZA_PP_ZZ_32 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 2048 =>
    (do
      (execute_UMOPS_ZA_PP_ZZ_32 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | _ => (pure (()))


def decode_SMOPA_ZA_PP_ZZ_64 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  let op1_unsigned : Bool := false
  let op2_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SMOPA_ZA_PP_ZZ_64 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 256 =>
    (do
      (execute_SMOPA_ZA_PP_ZZ_64 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 512 =>
    (do
      (execute_SMOPA_ZA_PP_ZZ_64 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 1024 =>
    (do
      (execute_SMOPA_ZA_PP_ZZ_64 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 2048 =>
    (do
      (execute_SMOPA_ZA_PP_ZZ_64 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | _ => (pure (()))


def decode_SUMOPA_ZA_PP_ZZ_64 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  let op1_unsigned : Bool := false
  let op2_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_SUMOPA_ZA_PP_ZZ_64 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 256 =>
    (do
      (execute_SUMOPA_ZA_PP_ZZ_64 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 512 =>
    (do
      (execute_SUMOPA_ZA_PP_ZZ_64 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 1024 =>
    (do
      (execute_SUMOPA_ZA_PP_ZZ_64 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 2048 =>
    (do
      (execute_SUMOPA_ZA_PP_ZZ_64 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | _ => (pure (()))


end ArmFull.Functions
