import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0115
import ArmFull.Fn.M0144
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0852
import ArmFull.Fn.M0889

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

def decode_EORTB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (tb : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  let sel1 : Nat := 1
  let sel2 : Nat := 0
  match VL with
  | 128 =>
    (do
      (execute_EORTB_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel1 sel2))
  | 256 =>
    (do
      (execute_EORTB_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel1 sel2))
  | 512 =>
    (do
      (execute_EORTB_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel1 sel2))
  | 1024 =>
    (do
      (execute_EORTB_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel1 sel2))
  | 2048 =>
    (do
      (execute_EORTB_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel1 sel2))
  | _ => (pure (()))


def decode_CDOT_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (rot : (BitVec 2)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((let b__0 := size
     (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 1 1)) == (0#1 : (BitVec 1))) : Bool)
     then true
     else false : Bool)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel_a : Int := (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])))
  let sel_b : Int :=
    (BitVec.toNat (Complement.complement (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)]))))
  let sub_i : Bool :=
    ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])) == (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
          rot 1)])))
  match VL with
  | 128 =>
    (do
      (execute_CDOT_Z_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i))
  | 256 =>
    (do
      (execute_CDOT_Z_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i))
  | 512 =>
    (do
      (execute_CDOT_Z_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i))
  | 1024 =>
    (do
      (execute_CDOT_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i))
  | 2048 =>
    (do
      (execute_CDOT_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i))
  | _ => (pure (()))


def decode_CDOT_Z_ZZZi_S (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (rot : (BitVec 2)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
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
  let index : Int := (BitVec.toNat i2)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel_a : Int := (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])))
  let sel_b : Int :=
    (BitVec.toNat (Complement.complement (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)]))))
  let sub_i : Bool :=
    ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])) == (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
          rot 1)])))
  match VL with
  | 128 =>
    (do
      (execute_CDOT_Z_ZZZi_S 128 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i))
  | 256 =>
    (do
      (execute_CDOT_Z_ZZZi_S 256 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i))
  | 512 =>
    (do
      (execute_CDOT_Z_ZZZi_S 512 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i))
  | 1024 =>
    (do
      (execute_CDOT_Z_ZZZi_S 1024 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i))
  | 2048 =>
    (do
      (execute_CDOT_Z_ZZZi_S 2048 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i))
  | _ => (pure (()))


def decode_CDOT_Z_ZZZi_D (size : (BitVec 2)) (i1 : (BitVec 1)) (Zm : (BitVec 4)) (rot : (BitVec 2)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
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
  let index : Int := (BitVec.toNat i1)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel_a : Int := (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])))
  let sel_b : Int :=
    (BitVec.toNat (Complement.complement (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)]))))
  let sub_i : Bool :=
    ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])) == (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
          rot 1)])))
  match VL with
  | 128 =>
    (do
      (execute_CDOT_Z_ZZZi_D 128 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i))
  | 256 =>
    (do
      (execute_CDOT_Z_ZZZi_D 256 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i))
  | 512 =>
    (do
      (execute_CDOT_Z_ZZZi_D 512 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i))
  | 1024 =>
    (do
      (execute_CDOT_Z_ZZZi_D 1024 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i))
  | 2048 =>
    (do
      (execute_CDOT_Z_ZZZi_D 2048 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i))
  | _ => (pure (()))


/-- Type quantifiers: VL : Nat, da : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned :
  Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SMMLA_Z_ZZZ__ (VL : Nat) (da : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Sail.BitVec.castWidth (Zeros (n := VL)))
  let op1 ← (( do (undefined_bitvector_at (← occLabel 5646) 128) ) : SailM (BitVec 128) )
  let op2 ← (( do (undefined_bitvector_at (← occLabel 5647) 128) ) : SailM (BitVec 128) )
  let addend ← (( do (undefined_bitvector_at (← occLabel 5648) 128) ) : SailM (BitVec 128) )
  let res ← (( do (undefined_bitvector_at (← occLabel 5649) 128) ) : SailM (BitVec 128) )
  let (addend, op1, op2, res, result) ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := (addend, op1, op2, res, result)
      for s in [loop_s_lower:loop_s_upper:1]i do
        let (addend, op1, op2, res, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Elem_read operand1 s 128) ) : SailM (BitVec 128) )
          let op1 := (w__0 : (BitVec 128))
          let w__1 ← (( do (Elem_read operand2 s 128) ) : SailM (BitVec 128) )
          let op2 := (w__1 : (BitVec 128))
          let w__2 ← (( do (Elem_read operand3 s 128) ) : SailM (BitVec 128) )
          let addend := (w__2 : (BitVec 128))
          let w__3 ← (( do (MatMulAdd (k_N := 128) addend op1 op2 op1_unsigned op2_unsigned) ) :
            SailM (BitVec 128) )
          let res := (w__3 : (BitVec 128))
          let w__4 ← (( do (Elem_set result s 128 res) ) : SailM (BitVec VL) )
          let result := (w__4 : (BitVec VL))
          (pure ((addend, op1, op2, res, result)))
      (pure loop_vars)) ) : SailM
    ((BitVec 128) × (BitVec 128) × (BitVec 128) × (BitVec 128) × (BitVec VL)) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned :
  Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_UMMLA_Z_ZZZ__ (VL : Nat) (da : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Sail.BitVec.castWidth (Zeros (n := VL)))
  let op1 ← (( do (undefined_bitvector_at (← occLabel 5650) 128) ) : SailM (BitVec 128) )
  let op2 ← (( do (undefined_bitvector_at (← occLabel 5651) 128) ) : SailM (BitVec 128) )
  let addend ← (( do (undefined_bitvector_at (← occLabel 5652) 128) ) : SailM (BitVec 128) )
  let res ← (( do (undefined_bitvector_at (← occLabel 5653) 128) ) : SailM (BitVec 128) )
  let (addend, op1, op2, res, result) ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := (addend, op1, op2, res, result)
      for s in [loop_s_lower:loop_s_upper:1]i do
        let (addend, op1, op2, res, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Elem_read operand1 s 128) ) : SailM (BitVec 128) )
          let op1 := (w__0 : (BitVec 128))
          let w__1 ← (( do (Elem_read operand2 s 128) ) : SailM (BitVec 128) )
          let op2 := (w__1 : (BitVec 128))
          let w__2 ← (( do (Elem_read operand3 s 128) ) : SailM (BitVec 128) )
          let addend := (w__2 : (BitVec 128))
          let w__3 ← (( do (MatMulAdd (k_N := 128) addend op1 op2 op1_unsigned op2_unsigned) ) :
            SailM (BitVec 128) )
          let res := (w__3 : (BitVec 128))
          let w__4 ← (( do (Elem_set result s 128 res) ) : SailM (BitVec VL) )
          let result := (w__4 : (BitVec VL))
          (pure ((addend, op1, op2, res, result)))
      (pure loop_vars)) ) : SailM
    ((BitVec 128) × (BitVec 128) × (BitVec 128) × (BitVec 128) × (BitVec VL)) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned :
  Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_USMMLA_Z_ZZZ__ (VL : Nat) (da : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Sail.BitVec.castWidth (Zeros (n := VL)))
  let op1 ← (( do (undefined_bitvector_at (← occLabel 5654) 128) ) : SailM (BitVec 128) )
  let op2 ← (( do (undefined_bitvector_at (← occLabel 5655) 128) ) : SailM (BitVec 128) )
  let addend ← (( do (undefined_bitvector_at (← occLabel 5656) 128) ) : SailM (BitVec 128) )
  let res ← (( do (undefined_bitvector_at (← occLabel 5657) 128) ) : SailM (BitVec 128) )
  let (addend, op1, op2, res, result) ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := (addend, op1, op2, res, result)
      for s in [loop_s_lower:loop_s_upper:1]i do
        let (addend, op1, op2, res, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Elem_read operand1 s 128) ) : SailM (BitVec 128) )
          let op1 := (w__0 : (BitVec 128))
          let w__1 ← (( do (Elem_read operand2 s 128) ) : SailM (BitVec 128) )
          let op2 := (w__1 : (BitVec 128))
          let w__2 ← (( do (Elem_read operand3 s 128) ) : SailM (BitVec 128) )
          let addend := (w__2 : (BitVec 128))
          let w__3 ← (( do (MatMulAdd (k_N := 128) addend op1 op2 op1_unsigned op2_unsigned) ) :
            SailM (BitVec 128) )
          let res := (w__3 : (BitVec 128))
          let w__4 ← (( do (Elem_set result s 128 res) ) : SailM (BitVec VL) )
          let result := (w__4 : (BitVec VL))
          (pure ((addend, op1, op2, res, result)))
      (pure loop_vars)) ) : SailM
    ((BitVec 128) × (BitVec 128) × (BitVec 128) × (BitVec 128) × (BitVec VL)) )
  (Z_set da VL (Sail.BitVec.castWidth result))


def decode_SQDMULH_Z_ZZi_H (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Zm : (BitVec 3)) (R : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
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
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_SQDMULH_Z_ZZi_H 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_SQDMULH_Z_ZZi_H 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_SQDMULH_Z_ZZi_H 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_SQDMULH_Z_ZZi_H 1024 (Sail.Int.toNatChecked (d)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_SQDMULH_Z_ZZi_H 2048 (Sail.Int.toNatChecked (d)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_SQDMULH_Z_ZZi_S (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (R : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
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
  let index : Int := (BitVec.toNat i2)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_SQDMULH_Z_ZZi_S 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_SQDMULH_Z_ZZi_S 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_SQDMULH_Z_ZZi_S 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_SQDMULH_Z_ZZi_S 1024 (Sail.Int.toNatChecked (d)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_SQDMULH_Z_ZZi_S 2048 (Sail.Int.toNatChecked (d)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_SQDMULH_Z_ZZi_D (size : (BitVec 2)) (i1 : (BitVec 1)) (Zm : (BitVec 4)) (R : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
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
  let index : Int := (BitVec.toNat i1)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_SQDMULH_Z_ZZi_D 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_SQDMULH_Z_ZZi_D 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_SQDMULH_Z_ZZi_D 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_SQDMULH_Z_ZZi_D 1024 (Sail.Int.toNatChecked (d)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_SQDMULH_Z_ZZi_D 2048 (Sail.Int.toNatChecked (d)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_SRSRA_Z_ZI__ (tszh : (BitVec 2)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (R : (BitVec 1)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let tsize : (BitVec 4) := (tszh +++ tszl)
  let esize : Int := 8
  let esize ← (( do
    match tsize with
    | 0b0000 => sailThrow ((Error_Undefined ()))
    | 0b0001 => (pure (8))
    | b__0 =>
      (let esize : Int :=
        if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b001#3 : (BitVec 3))) : Bool)
        then 16
        else
          (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b01#2 : (BitVec 2))) : Bool)
          then 32
          else 64)
      (pure (esize))) ) : SailM Int )
  let esize : Int := esize
  let n : Int := (BitVec.toNat Zn)
  let da : Int := (BitVec.toNat Zda)
  let shift : Int := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_SRSRA_Z_ZI__ 128 (Sail.Int.toNatChecked (da)) 8 (Sail.Int.toNatChecked (n)) shift))
      | 256 =>
        (do
          (execute_SRSRA_Z_ZI__ 256 (Sail.Int.toNatChecked (da)) 8 (Sail.Int.toNatChecked (n)) shift))
      | 512 =>
        (do
          (execute_SRSRA_Z_ZI__ 512 (Sail.Int.toNatChecked (da)) 8 (Sail.Int.toNatChecked (n)) shift))
      | 1024 =>
        (do
          (execute_SRSRA_Z_ZI__ 1024 (Sail.Int.toNatChecked (da)) 8 (Sail.Int.toNatChecked (n))
            shift))
      | 2048 =>
        (do
          (execute_SRSRA_Z_ZI__ 2048 (Sail.Int.toNatChecked (da)) 8 (Sail.Int.toNatChecked (n))
            shift))
      | _ => (pure (())))
  | 16 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_SRSRA_Z_ZI__ 128 (Sail.Int.toNatChecked (da)) 16 (Sail.Int.toNatChecked (n))
            shift))
      | 256 =>
        (do
          (execute_SRSRA_Z_ZI__ 256 (Sail.Int.toNatChecked (da)) 16 (Sail.Int.toNatChecked (n))
            shift))
      | 512 =>
        (do
          (execute_SRSRA_Z_ZI__ 512 (Sail.Int.toNatChecked (da)) 16 (Sail.Int.toNatChecked (n))
            shift))
      | 1024 =>
        (do
          (execute_SRSRA_Z_ZI__ 1024 (Sail.Int.toNatChecked (da)) 16 (Sail.Int.toNatChecked (n))
            shift))
      | 2048 =>
        (do
          (execute_SRSRA_Z_ZI__ 2048 (Sail.Int.toNatChecked (da)) 16 (Sail.Int.toNatChecked (n))
            shift))
      | _ => (pure (())))
  | 32 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_SRSRA_Z_ZI__ 128 (Sail.Int.toNatChecked (da)) 32 (Sail.Int.toNatChecked (n))
            shift))
      | 256 =>
        (do
          (execute_SRSRA_Z_ZI__ 256 (Sail.Int.toNatChecked (da)) 32 (Sail.Int.toNatChecked (n))
            shift))
      | 512 =>
        (do
          (execute_SRSRA_Z_ZI__ 512 (Sail.Int.toNatChecked (da)) 32 (Sail.Int.toNatChecked (n))
            shift))
      | 1024 =>
        (do
          (execute_SRSRA_Z_ZI__ 1024 (Sail.Int.toNatChecked (da)) 32 (Sail.Int.toNatChecked (n))
            shift))
      | 2048 =>
        (do
          (execute_SRSRA_Z_ZI__ 2048 (Sail.Int.toNatChecked (da)) 32 (Sail.Int.toNatChecked (n))
            shift))
      | _ => (pure (())))
  | 64 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_SRSRA_Z_ZI__ 128 (Sail.Int.toNatChecked (da)) 64 (Sail.Int.toNatChecked (n))
            shift))
      | 256 =>
        (do
          (execute_SRSRA_Z_ZI__ 256 (Sail.Int.toNatChecked (da)) 64 (Sail.Int.toNatChecked (n))
            shift))
      | 512 =>
        (do
          (execute_SRSRA_Z_ZI__ 512 (Sail.Int.toNatChecked (da)) 64 (Sail.Int.toNatChecked (n))
            shift))
      | 1024 =>
        (do
          (execute_SRSRA_Z_ZI__ 1024 (Sail.Int.toNatChecked (da)) 64 (Sail.Int.toNatChecked (n))
            shift))
      | 2048 =>
        (do
          (execute_SRSRA_Z_ZI__ 2048 (Sail.Int.toNatChecked (da)) 64 (Sail.Int.toNatChecked (n))
            shift))
      | _ => (pure (())))
  | _ =>
    (do
      ArmFull.assert false "sail-arm/instrs64_sve.sail:51742.22-51742.23"
      throw Error.Exit)


def decode_SSRA_Z_ZI__ (tszh : (BitVec 2)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (R : (BitVec 1)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let tsize : (BitVec 4) := (tszh +++ tszl)
  let esize : Int := 8
  let esize ← (( do
    match tsize with
    | 0b0000 => sailThrow ((Error_Undefined ()))
    | 0b0001 => (pure (8))
    | b__0 =>
      (let esize : Int :=
        if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b001#3 : (BitVec 3))) : Bool)
        then 16
        else
          (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b01#2 : (BitVec 2))) : Bool)
          then 32
          else 64)
      (pure (esize))) ) : SailM Int )
  let esize : Int := esize
  let n : Int := (BitVec.toNat Zn)
  let da : Int := (BitVec.toNat Zda)
  let shift : Int := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_SSRA_Z_ZI__ 128 (Sail.Int.toNatChecked (da)) 8 (Sail.Int.toNatChecked (n)) shift))
      | 256 =>
        (do
          (execute_SSRA_Z_ZI__ 256 (Sail.Int.toNatChecked (da)) 8 (Sail.Int.toNatChecked (n)) shift))
      | 512 =>
        (do
          (execute_SSRA_Z_ZI__ 512 (Sail.Int.toNatChecked (da)) 8 (Sail.Int.toNatChecked (n)) shift))
      | 1024 =>
        (do
          (execute_SSRA_Z_ZI__ 1024 (Sail.Int.toNatChecked (da)) 8 (Sail.Int.toNatChecked (n)) shift))
      | 2048 =>
        (do
          (execute_SSRA_Z_ZI__ 2048 (Sail.Int.toNatChecked (da)) 8 (Sail.Int.toNatChecked (n)) shift))
      | _ => (pure (())))
  | 16 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_SSRA_Z_ZI__ 128 (Sail.Int.toNatChecked (da)) 16 (Sail.Int.toNatChecked (n)) shift))
      | 256 =>
        (do
          (execute_SSRA_Z_ZI__ 256 (Sail.Int.toNatChecked (da)) 16 (Sail.Int.toNatChecked (n)) shift))
      | 512 =>
        (do
          (execute_SSRA_Z_ZI__ 512 (Sail.Int.toNatChecked (da)) 16 (Sail.Int.toNatChecked (n)) shift))
      | 1024 =>
        (do
          (execute_SSRA_Z_ZI__ 1024 (Sail.Int.toNatChecked (da)) 16 (Sail.Int.toNatChecked (n))
            shift))
      | 2048 =>
        (do
          (execute_SSRA_Z_ZI__ 2048 (Sail.Int.toNatChecked (da)) 16 (Sail.Int.toNatChecked (n))
            shift))
      | _ => (pure (())))
  | 32 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_SSRA_Z_ZI__ 128 (Sail.Int.toNatChecked (da)) 32 (Sail.Int.toNatChecked (n)) shift))
      | 256 =>
        (do
          (execute_SSRA_Z_ZI__ 256 (Sail.Int.toNatChecked (da)) 32 (Sail.Int.toNatChecked (n)) shift))
      | 512 =>
        (do
          (execute_SSRA_Z_ZI__ 512 (Sail.Int.toNatChecked (da)) 32 (Sail.Int.toNatChecked (n)) shift))
      | 1024 =>
        (do
          (execute_SSRA_Z_ZI__ 1024 (Sail.Int.toNatChecked (da)) 32 (Sail.Int.toNatChecked (n))
            shift))
      | 2048 =>
        (do
          (execute_SSRA_Z_ZI__ 2048 (Sail.Int.toNatChecked (da)) 32 (Sail.Int.toNatChecked (n))
            shift))
      | _ => (pure (())))
  | 64 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_SSRA_Z_ZI__ 128 (Sail.Int.toNatChecked (da)) 64 (Sail.Int.toNatChecked (n)) shift))
      | 256 =>
        (do
          (execute_SSRA_Z_ZI__ 256 (Sail.Int.toNatChecked (da)) 64 (Sail.Int.toNatChecked (n)) shift))
      | 512 =>
        (do
          (execute_SSRA_Z_ZI__ 512 (Sail.Int.toNatChecked (da)) 64 (Sail.Int.toNatChecked (n)) shift))
      | 1024 =>
        (do
          (execute_SSRA_Z_ZI__ 1024 (Sail.Int.toNatChecked (da)) 64 (Sail.Int.toNatChecked (n))
            shift))
      | 2048 =>
        (do
          (execute_SSRA_Z_ZI__ 2048 (Sail.Int.toNatChecked (da)) 64 (Sail.Int.toNatChecked (n))
            shift))
      | _ => (pure (())))
  | _ =>
    (do
      ArmFull.assert false "sail-arm/instrs64_sve.sail:51889.22-51889.23"
      throw Error.Exit)


end ArmFull.Functions
