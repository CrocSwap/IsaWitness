import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0051
import ArmFull.Fn.M0144
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0852
import ArmFull.Fn.M0868
import ArmFull.Fn.M0869

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

def decode_CLASTA_Z_P_ZZ__ (size : (BitVec 2)) (B : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let dn : Int := (BitVec.toNat Zdn)
  let m : Int := (BitVec.toNat Zm)
  let isBefore : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_CLASTA_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_CLASTA_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_CLASTA_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_CLASTA_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_CLASTA_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


def decode_CLASTB_Z_P_ZZ__ (size : (BitVec 2)) (B : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let dn : Int := (BitVec.toNat Zdn)
  let m : Int := (BitVec.toNat Zm)
  let isBefore : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_CLASTB_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_CLASTB_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_CLASTB_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_CLASTB_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_CLASTB_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_COMPACT_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand1 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Sail.BitVec.castWidth (Zeros (n := VL)))
  let x : Int := 0
  let (result, x) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (result, x)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (result, x) := loop_vars
        loop_vars ← do
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let element ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              let x : Int := x
              let w__3 ← (( do (Elem_set result x esize (Sail.BitVec.castWidth element)) ) : SailM
                (BitVec VL) )
              let result := (w__3 : (BitVec VL))
              let x : Int := (x +i 1)
              (pure ((result, x))))
          else (pure ((result, x)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (Z_set d VL (Sail.BitVec.castWidth result))


def decode_SPLICE_Z_P_ZZ_Des (size : (BitVec 2)) (Pv : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let v : Int := (BitVec.toNat Pv)
  let dst : Int := (BitVec.toNat Zdn)
  let s1 : Int := dst
  let s2 : Int := (BitVec.toNat Zm)
  match VL with
  | 128 =>
    (do
      (execute_SPLICE_Z_P_ZZ_Des 128 (Sail.Int.toNatChecked (dst)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (s1)) (Sail.Int.toNatChecked (s2)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_SPLICE_Z_P_ZZ_Des 256 (Sail.Int.toNatChecked (dst)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (s1)) (Sail.Int.toNatChecked (s2)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_SPLICE_Z_P_ZZ_Des 512 (Sail.Int.toNatChecked (dst)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (s1)) (Sail.Int.toNatChecked (s2)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_SPLICE_Z_P_ZZ_Des 1024 (Sail.Int.toNatChecked (dst)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (s1)) (Sail.Int.toNatChecked (s2)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_SPLICE_Z_P_ZZ_Des 2048 (Sail.Int.toNatChecked (dst)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (s1)) (Sail.Int.toNatChecked (s2)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_SPLICE_Z_P_ZZ_Con (size : (BitVec 2)) (Pv : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let v : Int := (BitVec.toNat Pv)
  let dst : Int := (BitVec.toNat Zd)
  let s1 : Int := (BitVec.toNat Zn)
  let s2 : Nat := (Nat.mod (Sail.Int.toNatChecked ((s1 +i 1))) 32)
  match VL with
  | 128 =>
    (do
      (execute_SPLICE_Z_P_ZZ_Con 128 (Sail.Int.toNatChecked (dst)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (s1)) s2 (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_SPLICE_Z_P_ZZ_Con 256 (Sail.Int.toNatChecked (dst)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (s1)) s2 (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_SPLICE_Z_P_ZZ_Con 512 (Sail.Int.toNatChecked (dst)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (s1)) s2 (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_SPLICE_Z_P_ZZ_Con 1024 (Sail.Int.toNatChecked (dst)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (s1)) s2 (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_SPLICE_Z_P_ZZ_Con 2048 (Sail.Int.toNatChecked (dst)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (s1)) s2 (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_EXT_Z_ZI_Des (imm8h : (BitVec 5)) (imm8l : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let dst : Int := (BitVec.toNat Zdn)
  let s1 : Int := dst
  let s2 : Int := (BitVec.toNat Zm)
  let position : Int := (BitVec.toNat (imm8h +++ imm8l))
  match VL with
  | 128 =>
    (do
      (execute_EXT_Z_ZI_Des 128 (Sail.Int.toNatChecked (dst)) esize
        (Sail.Int.toNatChecked (position)) (Sail.Int.toNatChecked (s1)) (Sail.Int.toNatChecked (s2))))
  | 256 =>
    (do
      (execute_EXT_Z_ZI_Des 256 (Sail.Int.toNatChecked (dst)) esize
        (Sail.Int.toNatChecked (position)) (Sail.Int.toNatChecked (s1)) (Sail.Int.toNatChecked (s2))))
  | 512 =>
    (do
      (execute_EXT_Z_ZI_Des 512 (Sail.Int.toNatChecked (dst)) esize
        (Sail.Int.toNatChecked (position)) (Sail.Int.toNatChecked (s1)) (Sail.Int.toNatChecked (s2))))
  | 1024 =>
    (do
      (execute_EXT_Z_ZI_Des 1024 (Sail.Int.toNatChecked (dst)) esize
        (Sail.Int.toNatChecked (position)) (Sail.Int.toNatChecked (s1)) (Sail.Int.toNatChecked (s2))))
  | 2048 =>
    (do
      (execute_EXT_Z_ZI_Des 2048 (Sail.Int.toNatChecked (dst)) esize
        (Sail.Int.toNatChecked (position)) (Sail.Int.toNatChecked (s1)) (Sail.Int.toNatChecked (s2))))
  | _ => (pure (()))


def decode_EXT_Z_ZI_Con (imm8h : (BitVec 5)) (imm8l : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let esize : Nat := 8
  let dst : Int := (BitVec.toNat Zd)
  let s1 : Int := (BitVec.toNat Zn)
  let s2 : Nat := (Nat.mod (Sail.Int.toNatChecked ((s1 +i 1))) 32)
  let position : Int := (BitVec.toNat (imm8h +++ imm8l))
  match VL with
  | 128 =>
    (do
      (execute_EXT_Z_ZI_Con 128 (Sail.Int.toNatChecked (dst)) esize
        (Sail.Int.toNatChecked (position)) (Sail.Int.toNatChecked (s1)) s2))
  | 256 =>
    (do
      (execute_EXT_Z_ZI_Con 256 (Sail.Int.toNatChecked (dst)) esize
        (Sail.Int.toNatChecked (position)) (Sail.Int.toNatChecked (s1)) s2))
  | 512 =>
    (do
      (execute_EXT_Z_ZI_Con 512 (Sail.Int.toNatChecked (dst)) esize
        (Sail.Int.toNatChecked (position)) (Sail.Int.toNatChecked (s1)) s2))
  | 1024 =>
    (do
      (execute_EXT_Z_ZI_Con 1024 (Sail.Int.toNatChecked (dst)) esize
        (Sail.Int.toNatChecked (position)) (Sail.Int.toNatChecked (s1)) s2))
  | 2048 =>
    (do
      (execute_EXT_Z_ZI_Con 2048 (Sail.Int.toNatChecked (dst)) esize
        (Sail.Int.toNatChecked (position)) (Sail.Int.toNatChecked (s1)) s2))
  | _ => (pure (()))


def decode_CPY_Z_P_R__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Rn)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_CPY_Z_P_R__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_CPY_Z_P_R__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_CPY_Z_P_R__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_CPY_Z_P_R__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_CPY_Z_P_R__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_CPY_Z_P_V__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Vn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Vn)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_CPY_Z_P_V__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_CPY_Z_P_V__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_CPY_Z_P_V__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_CPY_Z_P_V__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_CPY_Z_P_V__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_DUP_Z_Zi__ (imm2 : (BitVec 2)) (tsz : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let imm : (BitVec 7) := (imm2 +++ tsz)
  let esize : Int := 8
  let index ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 5405) 0 63))) ) :
    SailM Nat )
  let (esize, index) ← (( do
    match tsz with
    | 0b00000 => sailThrow ((Error_Undefined ()))
    | 0b10000 =>
      (let esize : Int := 128
      let index : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm 6 5))
      (pure ((esize, index))))
    | b__0 =>
      (let (esize, index) : (Int × Nat) :=
        if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 3 0)) == (0x8#4 : (BitVec 4))) : Bool)
        then
          (let esize : Int := 64
          let index : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm 6 4))
          (esize, index))
        else
          (let (esize, index) : (Int × Nat) :=
            if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 2 0)) == (0b100#3 : (BitVec 3))) : Bool)
            then
              (let esize : Int := 32
              let index : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm 6 3))
              (esize, index))
            else
              (let (esize, index) : (Int × Nat) :=
                if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 1 0)) == (0b10#2 : (BitVec 2))) : Bool)
                then
                  (let esize : Int := 16
                  let index : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm 6 2))
                  (esize, index))
                else
                  (let esize : Int := 8
                  let index : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm 6 1))
                  (esize, index))
              (esize, index))
          (esize, index))
      (pure ((esize, index)))) ) : SailM (Int × Nat) )
  let index : Int := index
  let esize : Int := esize
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_DUP_Z_Zi__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_DUP_Z_Zi__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_DUP_Z_Zi__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_DUP_Z_Zi__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_DUP_Z_Zi__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_DUP_Z_R__ (size : (BitVec 2)) (Rn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Rn)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_DUP_Z_R__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_DUP_Z_R__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_DUP_Z_R__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_DUP_Z_R__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_DUP_Z_R__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_LASTA_R_P_Z__ (size : (BitVec 2)) (B : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Rd : (BitVec 5)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let rsize : Nat :=
    if ((esize <b 64) : Bool)
    then 32
    else 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Rd)
  let isBefore : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_LASTA_R_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n)) rsize))
  | 256 =>
    (do
      (execute_LASTA_R_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n)) rsize))
  | 512 =>
    (do
      (execute_LASTA_R_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n)) rsize))
  | 1024 =>
    (do
      (execute_LASTA_R_P_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n)) rsize))
  | 2048 =>
    (do
      (execute_LASTA_R_P_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n)) rsize))
  | _ => (pure (()))


def decode_LASTB_R_P_Z__ (size : (BitVec 2)) (B : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Rd : (BitVec 5)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let rsize : Nat :=
    if ((esize <b 64) : Bool)
    then 32
    else 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Rd)
  let isBefore : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_LASTB_R_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n)) rsize))
  | 256 =>
    (do
      (execute_LASTB_R_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n)) rsize))
  | 512 =>
    (do
      (execute_LASTB_R_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n)) rsize))
  | 1024 =>
    (do
      (execute_LASTB_R_P_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n)) rsize))
  | 2048 =>
    (do
      (execute_LASTB_R_P_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n)) rsize))
  | _ => (pure (()))


def decode_LASTA_V_P_Z__ (size : (BitVec 2)) (B : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Vd)
  let isBefore : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_LASTA_V_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_LASTA_V_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_LASTA_V_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_LASTA_V_P_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_LASTA_V_P_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


end ArmFull.Functions
