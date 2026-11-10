import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0178
import ArmFull.Fn.M0202
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0852
import ArmFull.Fn.M1087
import ArmFull.Fn.M1121

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

def decode_BFDOT_Z_ZZZ__ (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
              (pure (((! w__0) : Bool)))) : Bool)
         then
           (do
             let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
             (pure (((! w__1) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        let w__3 ← (( do (HaveBF16Ext ()) ) : SailM Bool )
        (pure (((! w__3) : Bool)))) ) : SailM Bool )
  if (w__4 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  match VL with
  | 128 =>
    (do
      (execute_BFDOT_Z_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_BFDOT_Z_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_BFDOT_Z_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_BFDOT_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_BFDOT_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_BFDOT_Z_ZZZi__ (i2 : (BitVec 2)) (Zm : (BitVec 3)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
              (pure (((! w__0) : Bool)))) : Bool)
         then
           (do
             let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
             (pure (((! w__1) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        let w__3 ← (( do (HaveBF16Ext ()) ) : SailM Bool )
        (pure (((! w__3) : Bool)))) ) : SailM Bool )
  if (w__4 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let index : Int := (BitVec.toNat i2)
  match VL with
  | 128 =>
    (do
      (execute_BFDOT_Z_ZZZi__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_BFDOT_Z_ZZZi__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_BFDOT_Z_ZZZi__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_BFDOT_Z_ZZZi__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_BFDOT_Z_ZZZi__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_FDOT_Z_ZZZ__ (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  match VL with
  | 128 =>
    (do
      (execute_FDOT_Z_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FDOT_Z_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FDOT_Z_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FDOT_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FDOT_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_FDOT_Z_ZZZi__ (i2 : (BitVec 2)) (Zm : (BitVec 3)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let index : Int := (BitVec.toNat i2)
  match VL with
  | 128 =>
    (do
      (execute_FDOT_Z_ZZZi__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FDOT_Z_ZZZi__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FDOT_Z_ZZZi__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FDOT_Z_ZZZi__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FDOT_Z_ZZZi__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_BFCVT_Z_P_Z_S2BF (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
              (pure (((! w__0) : Bool)))) : Bool)
         then
           (do
             let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
             (pure (((! w__1) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        let w__3 ← (( do (HaveBF16Ext ()) ) : SailM Bool )
        (pure (((! w__3) : Bool)))) ) : SailM Bool )
  if (w__4 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_BFCVT_Z_P_Z_S2BF 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_BFCVT_Z_P_Z_S2BF 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_BFCVT_Z_P_Z_S2BF 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_BFCVT_Z_P_Z_S2BF 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_BFCVT_Z_P_Z_S2BF 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_BFCVTNT_Z_P_Z_S2BF (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
              (pure (((! w__0) : Bool)))) : Bool)
         then
           (do
             let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
             (pure (((! w__1) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        let w__3 ← (( do (HaveBF16Ext ()) ) : SailM Bool )
        (pure (((! w__3) : Bool)))) ) : SailM Bool )
  if (w__4 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_BFCVTNT_Z_P_Z_S2BF 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_BFCVTNT_Z_P_Z_S2BF 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_BFCVTNT_Z_P_Z_S2BF 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_BFCVTNT_Z_P_Z_S2BF 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_BFCVTNT_Z_P_Z_S2BF 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMMLA_Z_ZZZ_S (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((4 *i esize))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Sail.BitVec.castWidth (Zeros (n := VL)))
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5156)
      (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
  let op2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5157)
      (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
  let addend ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5158)
      (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
  let res ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5159)
      (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
  let (addend, op1, op2, res, result) ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := (addend, op1, op2, res, result)
      for s in [loop_s_lower:loop_s_upper:1]i do
        let (addend, op1, op2, res, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 s
              (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
          let op1 := (w__0 : (BitVec (4 * esize)))
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s
              (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
          let op2 := (w__1 : (BitVec (4 * esize)))
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 s
              (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
          let addend := (w__2 : (BitVec (4 * esize)))
          let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__4 ← (( do (FPMatMulAdd addend op1 op2 esize w__3) ) : SailM (BitVec (4 * esize))
            )
          let res := (w__4 : (BitVec (4 * esize)))
          let w__5 ← (( do
            (Elem_set result s (Sail.Int.toNatChecked ((4 *i esize))) (Sail.BitVec.castWidth res)) )
            : SailM (BitVec VL) )
          let result := (w__5 : (BitVec VL))
          (pure ((addend, op1, op2, res, result)))
      (pure loop_vars)) ) : SailM
    ((BitVec (4 * esize)) × (BitVec (4 * esize)) × (BitVec (4 * esize)) × (BitVec (4 * esize)) × (BitVec VL))
    )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 64 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMMLA_Z_ZZZ_D (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  if ((VL <b (esize *i 4)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let segments : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((4 *i esize))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Sail.BitVec.castWidth (Zeros (n := VL)))
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5160)
      (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
  let op2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5161)
      (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
  let addend ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5162)
      (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
  let res ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5163)
      (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
  let (addend, op1, op2, res, result) ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := (addend, op1, op2, res, result)
      for s in [loop_s_lower:loop_s_upper:1]i do
        let (addend, op1, op2, res, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 s
              (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
          let op1 := (w__0 : (BitVec (4 * esize)))
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s
              (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
          let op2 := (w__1 : (BitVec (4 * esize)))
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 s
              (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
          let addend := (w__2 : (BitVec (4 * esize)))
          let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__4 ← (( do (FPMatMulAdd addend op1 op2 esize w__3) ) : SailM (BitVec (4 * esize))
            )
          let res := (w__4 : (BitVec (4 * esize)))
          let w__5 ← (( do
            (Elem_set result s (Sail.Int.toNatChecked ((4 *i esize))) (Sail.BitVec.castWidth res)) )
            : SailM (BitVec VL) )
          let result := (w__5 : (BitVec VL))
          (pure ((addend, op1, op2, res, result)))
      (pure loop_vars)) ) : SailM
    ((BitVec (4 * esize)) × (BitVec (4 * esize)) × (BitVec (4 * esize)) × (BitVec (4 * esize)) × (BitVec VL))
    )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFMMLA_Z_ZZZ__ (VL : Nat) (da : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5164)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let op1 ← (( do (undefined_bitvector_at (← occLabel 5165) 128) ) : SailM (BitVec 128) )
  let op2 ← (( do (undefined_bitvector_at (← occLabel 5166) 128) ) : SailM (BitVec 128) )
  let addend ← (( do (undefined_bitvector_at (← occLabel 5167) 128) ) : SailM (BitVec 128) )
  let res ← (( do (undefined_bitvector_at (← occLabel 5168) 128) ) : SailM (BitVec 128) )
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
          let w__3 ← (( do (BFMatMulAdd (k_N := 128) addend op1 op2) ) : SailM (BitVec 128) )
          let res := (w__3 : (BitVec 128))
          let w__4 ← (( do (Elem_set result s 128 res) ) : SailM (BitVec VL) )
          let result := (w__4 : (BitVec VL))
          (pure ((addend, op1, op2, res, result)))
      (pure loop_vars)) ) : SailM
    ((BitVec 128) × (BitVec 128) × (BitVec 128) × (BitVec 128) × (BitVec VL)) )
  (Z_set da VL (Sail.BitVec.castWidth result))


def decode_FCVTNT_Z_P_Z_D2S (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_FCVTNT_Z_P_Z_D2S 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FCVTNT_Z_P_Z_D2S 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FCVTNT_Z_P_Z_D2S 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FCVTNT_Z_P_Z_D2S 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FCVTNT_Z_P_Z_D2S 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_FCVTNT_Z_P_Z_S2H (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_FCVTNT_Z_P_Z_S2H 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FCVTNT_Z_P_Z_S2H 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FCVTNT_Z_P_Z_S2H 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FCVTNT_Z_P_Z_S2H 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FCVTNT_Z_P_Z_S2H 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_FCVTLT_Z_P_Z_S2D (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_FCVTLT_Z_P_Z_S2D 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FCVTLT_Z_P_Z_S2D 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FCVTLT_Z_P_Z_S2D 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FCVTLT_Z_P_Z_S2D 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FCVTLT_Z_P_Z_S2D 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_FCVTLT_Z_P_Z_H2S (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_FCVTLT_Z_P_Z_H2S 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FCVTLT_Z_P_Z_H2S 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FCVTLT_Z_P_Z_H2S 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FCVTLT_Z_P_Z_H2S 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FCVTLT_Z_P_Z_H2S 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_FCVTX_Z_P_Z_D2S (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let s_esize : Nat := 64
  let d_esize : Nat := 32
  match VL with
  | 128 =>
    (do
      (execute_FCVTX_Z_P_Z_D2S 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 256 =>
    (do
      (execute_FCVTX_Z_P_Z_D2S 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 512 =>
    (do
      (execute_FCVTX_Z_P_Z_D2S 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 1024 =>
    (do
      (execute_FCVTX_Z_P_Z_D2S 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | 2048 =>
    (do
      (execute_FCVTX_Z_P_Z_D2S 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
  | _ => (pure (()))


end ArmFull.Functions
