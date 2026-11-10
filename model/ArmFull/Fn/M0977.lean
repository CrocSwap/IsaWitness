import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0045
import ArmFull.Fn.M0046
import ArmFull.Fn.M0114
import ArmFull.Fn.M0144
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0840
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

def decode_URSRA_Z_ZI__ (tszh : (BitVec 2)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (R : (BitVec 1)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
          (execute_URSRA_Z_ZI__ 128 (Sail.Int.toNatChecked (da)) 8 (Sail.Int.toNatChecked (n)) shift))
      | 256 =>
        (do
          (execute_URSRA_Z_ZI__ 256 (Sail.Int.toNatChecked (da)) 8 (Sail.Int.toNatChecked (n)) shift))
      | 512 =>
        (do
          (execute_URSRA_Z_ZI__ 512 (Sail.Int.toNatChecked (da)) 8 (Sail.Int.toNatChecked (n)) shift))
      | 1024 =>
        (do
          (execute_URSRA_Z_ZI__ 1024 (Sail.Int.toNatChecked (da)) 8 (Sail.Int.toNatChecked (n))
            shift))
      | 2048 =>
        (do
          (execute_URSRA_Z_ZI__ 2048 (Sail.Int.toNatChecked (da)) 8 (Sail.Int.toNatChecked (n))
            shift))
      | _ => (pure (())))
  | 16 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_URSRA_Z_ZI__ 128 (Sail.Int.toNatChecked (da)) 16 (Sail.Int.toNatChecked (n))
            shift))
      | 256 =>
        (do
          (execute_URSRA_Z_ZI__ 256 (Sail.Int.toNatChecked (da)) 16 (Sail.Int.toNatChecked (n))
            shift))
      | 512 =>
        (do
          (execute_URSRA_Z_ZI__ 512 (Sail.Int.toNatChecked (da)) 16 (Sail.Int.toNatChecked (n))
            shift))
      | 1024 =>
        (do
          (execute_URSRA_Z_ZI__ 1024 (Sail.Int.toNatChecked (da)) 16 (Sail.Int.toNatChecked (n))
            shift))
      | 2048 =>
        (do
          (execute_URSRA_Z_ZI__ 2048 (Sail.Int.toNatChecked (da)) 16 (Sail.Int.toNatChecked (n))
            shift))
      | _ => (pure (())))
  | 32 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_URSRA_Z_ZI__ 128 (Sail.Int.toNatChecked (da)) 32 (Sail.Int.toNatChecked (n))
            shift))
      | 256 =>
        (do
          (execute_URSRA_Z_ZI__ 256 (Sail.Int.toNatChecked (da)) 32 (Sail.Int.toNatChecked (n))
            shift))
      | 512 =>
        (do
          (execute_URSRA_Z_ZI__ 512 (Sail.Int.toNatChecked (da)) 32 (Sail.Int.toNatChecked (n))
            shift))
      | 1024 =>
        (do
          (execute_URSRA_Z_ZI__ 1024 (Sail.Int.toNatChecked (da)) 32 (Sail.Int.toNatChecked (n))
            shift))
      | 2048 =>
        (do
          (execute_URSRA_Z_ZI__ 2048 (Sail.Int.toNatChecked (da)) 32 (Sail.Int.toNatChecked (n))
            shift))
      | _ => (pure (())))
  | 64 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_URSRA_Z_ZI__ 128 (Sail.Int.toNatChecked (da)) 64 (Sail.Int.toNatChecked (n))
            shift))
      | 256 =>
        (do
          (execute_URSRA_Z_ZI__ 256 (Sail.Int.toNatChecked (da)) 64 (Sail.Int.toNatChecked (n))
            shift))
      | 512 =>
        (do
          (execute_URSRA_Z_ZI__ 512 (Sail.Int.toNatChecked (da)) 64 (Sail.Int.toNatChecked (n))
            shift))
      | 1024 =>
        (do
          (execute_URSRA_Z_ZI__ 1024 (Sail.Int.toNatChecked (da)) 64 (Sail.Int.toNatChecked (n))
            shift))
      | 2048 =>
        (do
          (execute_URSRA_Z_ZI__ 2048 (Sail.Int.toNatChecked (da)) 64 (Sail.Int.toNatChecked (n))
            shift))
      | _ => (pure (())))
  | _ =>
    (do
      ArmFull.assert false "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:52036.22-52036.23"
      throw Error.Exit)


def decode_USRA_Z_ZI__ (tszh : (BitVec 2)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (R : (BitVec 1)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
          (execute_USRA_Z_ZI__ 128 (Sail.Int.toNatChecked (da)) 8 (Sail.Int.toNatChecked (n)) shift))
      | 256 =>
        (do
          (execute_USRA_Z_ZI__ 256 (Sail.Int.toNatChecked (da)) 8 (Sail.Int.toNatChecked (n)) shift))
      | 512 =>
        (do
          (execute_USRA_Z_ZI__ 512 (Sail.Int.toNatChecked (da)) 8 (Sail.Int.toNatChecked (n)) shift))
      | 1024 =>
        (do
          (execute_USRA_Z_ZI__ 1024 (Sail.Int.toNatChecked (da)) 8 (Sail.Int.toNatChecked (n)) shift))
      | 2048 =>
        (do
          (execute_USRA_Z_ZI__ 2048 (Sail.Int.toNatChecked (da)) 8 (Sail.Int.toNatChecked (n)) shift))
      | _ => (pure (())))
  | 16 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_USRA_Z_ZI__ 128 (Sail.Int.toNatChecked (da)) 16 (Sail.Int.toNatChecked (n)) shift))
      | 256 =>
        (do
          (execute_USRA_Z_ZI__ 256 (Sail.Int.toNatChecked (da)) 16 (Sail.Int.toNatChecked (n)) shift))
      | 512 =>
        (do
          (execute_USRA_Z_ZI__ 512 (Sail.Int.toNatChecked (da)) 16 (Sail.Int.toNatChecked (n)) shift))
      | 1024 =>
        (do
          (execute_USRA_Z_ZI__ 1024 (Sail.Int.toNatChecked (da)) 16 (Sail.Int.toNatChecked (n))
            shift))
      | 2048 =>
        (do
          (execute_USRA_Z_ZI__ 2048 (Sail.Int.toNatChecked (da)) 16 (Sail.Int.toNatChecked (n))
            shift))
      | _ => (pure (())))
  | 32 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_USRA_Z_ZI__ 128 (Sail.Int.toNatChecked (da)) 32 (Sail.Int.toNatChecked (n)) shift))
      | 256 =>
        (do
          (execute_USRA_Z_ZI__ 256 (Sail.Int.toNatChecked (da)) 32 (Sail.Int.toNatChecked (n)) shift))
      | 512 =>
        (do
          (execute_USRA_Z_ZI__ 512 (Sail.Int.toNatChecked (da)) 32 (Sail.Int.toNatChecked (n)) shift))
      | 1024 =>
        (do
          (execute_USRA_Z_ZI__ 1024 (Sail.Int.toNatChecked (da)) 32 (Sail.Int.toNatChecked (n))
            shift))
      | 2048 =>
        (do
          (execute_USRA_Z_ZI__ 2048 (Sail.Int.toNatChecked (da)) 32 (Sail.Int.toNatChecked (n))
            shift))
      | _ => (pure (())))
  | 64 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_USRA_Z_ZI__ 128 (Sail.Int.toNatChecked (da)) 64 (Sail.Int.toNatChecked (n)) shift))
      | 256 =>
        (do
          (execute_USRA_Z_ZI__ 256 (Sail.Int.toNatChecked (da)) 64 (Sail.Int.toNatChecked (n)) shift))
      | 512 =>
        (do
          (execute_USRA_Z_ZI__ 512 (Sail.Int.toNatChecked (da)) 64 (Sail.Int.toNatChecked (n)) shift))
      | 1024 =>
        (do
          (execute_USRA_Z_ZI__ 1024 (Sail.Int.toNatChecked (da)) 64 (Sail.Int.toNatChecked (n))
            shift))
      | 2048 =>
        (do
          (execute_USRA_Z_ZI__ 2048 (Sail.Int.toNatChecked (da)) 64 (Sail.Int.toNatChecked (n))
            shift))
      | _ => (pure (())))
  | _ =>
    (do
      ArmFull.assert false "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:52183.22-52183.23"
      throw Error.Exit)


/-- Type quantifiers: VL : Nat, dn : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_AESD_Z_ZZ__ (VL : Nat) (dn : Nat) (m : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (operand1 ^^^ operand2)
  let result ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := result
      for s in [loop_s_lower:loop_s_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Elem_read result s 128) ) : SailM (BitVec 128) )
          let w__1 ← (( do (AESInvSubBytes (AESInvShiftRows w__0)) ) : SailM (BitVec 128) )
          (Elem_set result s 128 w__1)
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_AESE_Z_ZZ__ (VL : Nat) (dn : Nat) (m : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (operand1 ^^^ operand2)
  let result ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := result
      for s in [loop_s_lower:loop_s_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Elem_read result s 128) ) : SailM (BitVec 128) )
          let w__1 ← (( do (AESSubBytes (AESShiftRows w__0)) ) : SailM (BitVec 128) )
          (Elem_set result s 128 w__1)
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_AESIMC_Z_Z__ (VL : Nat) (dn : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5665)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := result
      for s in [loop_s_lower:loop_s_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Elem_read operand s 128) ) : SailM (BitVec 128) )
          let w__1 ← (( do (AESInvMixColumns w__0) ) : SailM (BitVec 128) )
          (Elem_set result s 128 w__1)
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_AESMC_Z_Z__ (VL : Nat) (dn : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5666)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := result
      for s in [loop_s_lower:loop_s_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Elem_read operand s 128) ) : SailM (BitVec 128) )
          let w__1 ← (( do (AESMixColumns w__0) ) : SailM (BitVec 128) )
          (Elem_set result s 128 w__1)
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_RAX1_Z_ZZ__ (VL : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (CheckSVEEnabled ()))
  else
    (do
      (CheckNonStreamingSVEEnabled ()))
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 64)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5667)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (Elem_read operand1 e 64) ) : SailM (BitVec 64) )
          let element2 ← (( do (Elem_read operand2 e 64) ) : SailM (BitVec 64) )
          let w__1 ← (( do (ROL element2 1) ) : SailM (BitVec 64) )
          (Elem_set result e 64 (element1 ^^^ w__1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SM4E_Z_ZZ__ (VL : Nat) (dn : Nat) (m : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5668)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := result
      for s in [loop_s_lower:loop_s_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let key ← (( do (Elem_read operand2 s 128) ) : SailM (BitVec 128) )
          let intval ← (( do (undefined_bitvector_at (← occLabel 5669) 32) ) : SailM (BitVec 32)
            )
          let sboxout ← (( do (undefined_bitvector_at (← occLabel 5670) 8) ) : SailM (BitVec 8)
            )
          let roundresult ← (( do (Elem_read operand1 s 128) ) : SailM (BitVec 128) )
          let roundkey ← (( do (undefined_bitvector_at (← occLabel 5671) 32) ) : SailM
            (BitVec 32) )
          let (intval, roundkey, roundresult) ← (( do
            let loop_index_lower : Nat := 0
            let loop_index_upper : Nat := 3
            (do
              let mut loop_vars_1 := (intval, roundkey, roundresult)
              for index in [loop_index_lower:loop_index_upper:1]i do
                let (intval, roundkey, roundresult) := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do (Elem_read key index 32) ) : SailM (BitVec 32) )
                  let roundkey := (w__0 : (BitVec 32))
                  let intval : (BitVec 32) :=
                    ((Sail.BitVec.castWidth (m := 32) ((Sail.BitVec.castWidth (m := 32) ((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                            roundresult 127 96)) ^^^ (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                            roundresult 95 64)))) ^^^ (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                          roundresult 63 32)))) ^^^ roundkey)
                  let intval ← (( do
                    let loop_i_lower : Nat := 0
                    let loop_i_upper : Nat := 3
                    (do
                      let mut loop_vars_2 := intval
                      for i in [loop_i_lower:loop_i_upper:1]i do
                        let intval := loop_vars_2
                        loop_vars_2 ← do
                          let w__1 ← (( do (Elem_read intval i 8) ) : SailM (BitVec 8) )
                          (Elem_set intval i 8 (Sbox w__1))
                      (pure loop_vars_2)) ) : SailM (BitVec 32) )
                  let w__3 ← (( do (ROL intval 2) ) : SailM (BitVec 32) )
                  let w__4 ← (( do (ROL intval 10) ) : SailM (BitVec 32) )
                  let w__5 ← (( do (ROL intval 18) ) : SailM (BitVec 32) )
                  let w__6 ← (( do (ROL intval 24) ) : SailM (BitVec 32) )
                  let intval := (((((intval ^^^ w__3) ^^^ w__4) ^^^ w__5) ^^^ w__6) : (BitVec 32))
                  let intval : (BitVec 32) :=
                    (intval ^^^ (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb roundresult
                        31 0)))
                  let roundresult : (BitVec 128) :=
                    (Sail.BitVec.updateSubrange roundresult 31 0
                      (Sail.BitVec.extractLsb roundresult 63 32))
                  let roundresult : (BitVec 128) :=
                    (Sail.BitVec.updateSubrange roundresult 63 32
                      (Sail.BitVec.extractLsb roundresult 95 64))
                  let roundresult : (BitVec 128) :=
                    (Sail.BitVec.updateSubrange roundresult 95 64
                      (Sail.BitVec.extractLsb roundresult 127 96))
                  let roundresult : (BitVec 128) :=
                    (Sail.BitVec.updateSubrange roundresult 127 96 intval)
                  (pure ((intval, roundkey, roundresult)))
              (pure loop_vars_1)) ) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 128)) )
          (Elem_set result s 128 roundresult)
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SM4EKEY_Z_ZZ__ (VL : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5672)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := result
      for s in [loop_s_lower:loop_s_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let source ← (( do (Elem_read operand2 s 128) ) : SailM (BitVec 128) )
          let intval ← (( do (undefined_bitvector_at (← occLabel 5673) 32) ) : SailM (BitVec 32)
            )
          let sboxout ← (( do (undefined_bitvector_at (← occLabel 5674) 8) ) : SailM (BitVec 8)
            )
          let const ← (( do (undefined_bitvector_at (← occLabel 5675) 32) ) : SailM (BitVec 32)
            )
          let roundresult ← (( do (Elem_read operand1 s 128) ) : SailM (BitVec 128) )
          let (const, intval, roundresult) ← (( do
            let loop_index_lower : Nat := 0
            let loop_index_upper : Nat := 3
            (do
              let mut loop_vars_1 := (const, intval, roundresult)
              for index in [loop_index_lower:loop_index_upper:1]i do
                let (const, intval, roundresult) := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do (Elem_read source index 32) ) : SailM (BitVec 32) )
                  let const := (w__0 : (BitVec 32))
                  let intval : (BitVec 32) :=
                    ((Sail.BitVec.castWidth (m := 32) ((Sail.BitVec.castWidth (m := 32) ((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                            roundresult 127 96)) ^^^ (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                            roundresult 95 64)))) ^^^ (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                          roundresult 63 32)))) ^^^ const)
                  let intval ← (( do
                    let loop_i_lower : Nat := 0
                    let loop_i_upper : Nat := 3
                    (do
                      let mut loop_vars_2 := intval
                      for i in [loop_i_lower:loop_i_upper:1]i do
                        let intval := loop_vars_2
                        loop_vars_2 ← do
                          let w__1 ← (( do (Elem_read intval i 8) ) : SailM (BitVec 8) )
                          (Elem_set intval i 8 (Sbox w__1))
                      (pure loop_vars_2)) ) : SailM (BitVec 32) )
                  let w__3 ← (( do (ROL intval 13) ) : SailM (BitVec 32) )
                  let w__4 ← (( do (ROL intval 23) ) : SailM (BitVec 32) )
                  let intval := (((intval ^^^ w__3) ^^^ w__4) : (BitVec 32))
                  let intval : (BitVec 32) :=
                    (intval ^^^ (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb roundresult
                        31 0)))
                  let roundresult : (BitVec 128) :=
                    (Sail.BitVec.updateSubrange roundresult 31 0
                      (Sail.BitVec.extractLsb roundresult 63 32))
                  let roundresult : (BitVec 128) :=
                    (Sail.BitVec.updateSubrange roundresult 63 32
                      (Sail.BitVec.extractLsb roundresult 95 64))
                  let roundresult : (BitVec 128) :=
                    (Sail.BitVec.updateSubrange roundresult 95 64
                      (Sail.BitVec.extractLsb roundresult 127 96))
                  let roundresult : (BitVec 128) :=
                    (Sail.BitVec.updateSubrange roundresult 127 96 intval)
                  (pure ((const, intval, roundresult)))
              (pure loop_vars_1)) ) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 128)) )
          (Elem_set result s 128 roundresult)
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


def decode_XAR_Z_ZZI__ (tszh : (BitVec 2)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let m : Int := (BitVec.toNat Zm)
  let dn : Int := (BitVec.toNat Zdn)
  let rot : Int := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_XAR_Z_ZZI__ 128 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (m)) rot))
      | 256 =>
        (do
          (execute_XAR_Z_ZZI__ 256 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (m)) rot))
      | 512 =>
        (do
          (execute_XAR_Z_ZZI__ 512 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (m)) rot))
      | 1024 =>
        (do
          (execute_XAR_Z_ZZI__ 1024 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (m)) rot))
      | 2048 =>
        (do
          (execute_XAR_Z_ZZI__ 2048 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (m)) rot))
      | _ => (pure (())))
  | 16 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_XAR_Z_ZZI__ 128 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (m)) rot))
      | 256 =>
        (do
          (execute_XAR_Z_ZZI__ 256 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (m)) rot))
      | 512 =>
        (do
          (execute_XAR_Z_ZZI__ 512 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (m)) rot))
      | 1024 =>
        (do
          (execute_XAR_Z_ZZI__ 1024 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (m)) rot))
      | 2048 =>
        (do
          (execute_XAR_Z_ZZI__ 2048 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (m)) rot))
      | _ => (pure (())))
  | 32 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_XAR_Z_ZZI__ 128 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (m)) rot))
      | 256 =>
        (do
          (execute_XAR_Z_ZZI__ 256 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (m)) rot))
      | 512 =>
        (do
          (execute_XAR_Z_ZZI__ 512 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (m)) rot))
      | 1024 =>
        (do
          (execute_XAR_Z_ZZI__ 1024 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (m)) rot))
      | 2048 =>
        (do
          (execute_XAR_Z_ZZI__ 2048 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (m)) rot))
      | _ => (pure (())))
  | 64 =>
    (do
      match VL with
      | 128 =>
        (do
          (execute_XAR_Z_ZZI__ 128 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (m)) rot))
      | 256 =>
        (do
          (execute_XAR_Z_ZZI__ 256 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (m)) rot))
      | 512 =>
        (do
          (execute_XAR_Z_ZZI__ 512 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (m)) rot))
      | 1024 =>
        (do
          (execute_XAR_Z_ZZI__ 1024 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (m)) rot))
      | 2048 =>
        (do
          (execute_XAR_Z_ZZI__ 2048 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (m)) rot))
      | _ => (pure (())))
  | _ =>
    (do
      ArmFull.assert false "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:52750.22-52750.23"
      throw Error.Exit)


end ArmFull.Functions
