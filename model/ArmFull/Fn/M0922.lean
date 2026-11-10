import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0087
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0204
import ArmFull.Fn.M0215
import ArmFull.Fn.M0238
import ArmFull.Fn.M0840
import ArmFull.Fn.M0849
import ArmFull.Fn.M0850

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

def decode_LUTI4_MZ2_ZTZ_1 (i2 : (BitVec 2)) (size : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let isize : Nat := 4
  let n : Int := (BitVec.toNat Zn)
  let dstride : Nat := 1
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  let imm : Int := (BitVec.toNat i2)
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_LUTI4_MZ2_ZTZ_1 128 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 256 =>
    (do
      (execute_LUTI4_MZ2_ZTZ_1 256 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 512 =>
    (do
      (execute_LUTI4_MZ2_ZTZ_1 512 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 1024 =>
    (do
      (execute_LUTI4_MZ2_ZTZ_1 1024 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 2048 =>
    (do
      (execute_LUTI4_MZ2_ZTZ_1 2048 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | _ => (pure (()))


def decode_LUTI2_MZ4_ZTZ_1 (i2 : (BitVec 2)) (size : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let isize : Nat := 2
  let n : Int := (BitVec.toNat Zn)
  let dstride : Nat := 1
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let imm : Int := (BitVec.toNat i2)
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_LUTI2_MZ4_ZTZ_1 128 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 256 =>
    (do
      (execute_LUTI2_MZ4_ZTZ_1 256 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 512 =>
    (do
      (execute_LUTI2_MZ4_ZTZ_1 512 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 1024 =>
    (do
      (execute_LUTI2_MZ4_ZTZ_1 1024 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 2048 =>
    (do
      (execute_LUTI2_MZ4_ZTZ_1 2048 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | _ => (pure (()))


def decode_LUTI4_MZ4_ZTZ_1 (i1 : (BitVec 1)) (size : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let isize : Nat := 4
  let n : Int := (BitVec.toNat Zn)
  let dstride : Nat := 1
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let imm : Int := (BitVec.toNat i1)
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_LUTI4_MZ4_ZTZ_1 128 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 256 =>
    (do
      (execute_LUTI4_MZ4_ZTZ_1 256 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 512 =>
    (do
      (execute_LUTI4_MZ4_ZTZ_1 512 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 1024 =>
    (do
      (execute_LUTI4_MZ4_ZTZ_1 1024 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 2048 =>
    (do
      (execute_LUTI4_MZ4_ZTZ_1 2048 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | _ => (pure (()))


/-- Type quantifiers: VL : Nat, ngrp : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ ngrp = 2 ∧ (is_VL VL) -/
def execute_ZERO_ZA1_RI_2 (VL : Nat) (ngrp : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name ngrp)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let vec ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((ngrp -i 1)))
    (do
      let mut loop_vars := vec
      for r in [loop_r_lower:loop_r_upper:1]i do
        let vec := loop_vars
        loop_vars ← do
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth (Zeros (n := VL))))
          let vec : Int := (vec +i vstride)
          (pure (vec))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: VL : Nat, ngrp : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ ngrp = 4 ∧ (is_VL VL) -/
def execute_ZERO_ZA1_RI_4 (VL : Nat) (ngrp : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name ngrp)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let vec ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((ngrp -i 1)))
    (do
      let mut loop_vars := vec
      for r in [loop_r_lower:loop_r_upper:1]i do
        let vec := loop_vars
        loop_vars ← do
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth (Zeros (n := VL))))
          let vec : Int := (vec +i vstride)
          (pure (vec))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: VL : Nat, ngrp : Nat, nvec : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nvec = 2 ∧ ngrp = 1 ∧ (is_VL VL) -/
def execute_ZERO_ZA2_RI_1 (VL : Nat) (ngrp : Nat) (nvec : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name ngrp)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let vec : Int := (vec -i (fmod_int vec nvec))
  let vec ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((ngrp -i 1)))
    (do
      let mut loop_vars := vec
      for r in [loop_r_lower:loop_r_upper:1]i do
        let vec := loop_vars
        loop_vars ← do
          let vec : Int := vec
          let loop_i_lower : Nat := 0
          let loop_i_upper : Nat := (Sail.Int.toNatChecked ((nvec -i 1)))
          (do
            let mut loop_vars_1 := ()
            for i in [loop_i_lower:loop_i_upper:1]i do
              let () := loop_vars_1
              loop_vars_1 ← do
                (ZAvector_set (vec +i i) VL (Sail.BitVec.castWidth (Zeros (n := VL))))
            (pure loop_vars_1))
          let vec : Int := (vec +i vstride)
          (pure (vec))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: VL : Nat, ngrp : Nat, nvec : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nvec = 2 ∧ ngrp = 2 ∧ (is_VL VL) -/
def execute_ZERO_ZA2_RI_2 (VL : Nat) (ngrp : Nat) (nvec : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name ngrp)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let vec : Int := (vec -i (fmod_int vec nvec))
  let vec ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((ngrp -i 1)))
    (do
      let mut loop_vars := vec
      for r in [loop_r_lower:loop_r_upper:1]i do
        let vec := loop_vars
        loop_vars ← do
          let vec : Int := vec
          let loop_i_lower : Nat := 0
          let loop_i_upper : Nat := (Sail.Int.toNatChecked ((nvec -i 1)))
          (do
            let mut loop_vars_1 := ()
            for i in [loop_i_lower:loop_i_upper:1]i do
              let () := loop_vars_1
              loop_vars_1 ← do
                (ZAvector_set (vec +i i) VL (Sail.BitVec.castWidth (Zeros (n := VL))))
            (pure loop_vars_1))
          let vec : Int := (vec +i vstride)
          (pure (vec))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: VL : Nat, ngrp : Nat, nvec : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nvec = 2 ∧ ngrp = 4 ∧ (is_VL VL) -/
def execute_ZERO_ZA2_RI_4 (VL : Nat) (ngrp : Nat) (nvec : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name ngrp)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let vec : Int := (vec -i (fmod_int vec nvec))
  let vec ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((ngrp -i 1)))
    (do
      let mut loop_vars := vec
      for r in [loop_r_lower:loop_r_upper:1]i do
        let vec := loop_vars
        loop_vars ← do
          let vec : Int := vec
          let loop_i_lower : Nat := 0
          let loop_i_upper : Nat := (Sail.Int.toNatChecked ((nvec -i 1)))
          (do
            let mut loop_vars_1 := ()
            for i in [loop_i_lower:loop_i_upper:1]i do
              let () := loop_vars_1
              loop_vars_1 ← do
                (ZAvector_set (vec +i i) VL (Sail.BitVec.castWidth (Zeros (n := VL))))
            (pure loop_vars_1))
          let vec : Int := (vec +i vstride)
          (pure (vec))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: VL : Nat, ngrp : Nat, nvec : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nvec = 4 ∧ ngrp = 1 ∧ (is_VL VL) -/
def execute_ZERO_ZA4_RI_1 (VL : Nat) (ngrp : Nat) (nvec : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name ngrp)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let vec : Int := (vec -i (fmod_int vec nvec))
  let vec ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((ngrp -i 1)))
    (do
      let mut loop_vars := vec
      for r in [loop_r_lower:loop_r_upper:1]i do
        let vec := loop_vars
        loop_vars ← do
          let vec : Int := vec
          let loop_i_lower : Nat := 0
          let loop_i_upper : Nat := (Sail.Int.toNatChecked ((nvec -i 1)))
          (do
            let mut loop_vars_1 := ()
            for i in [loop_i_lower:loop_i_upper:1]i do
              let () := loop_vars_1
              loop_vars_1 ← do
                (ZAvector_set (vec +i i) VL (Sail.BitVec.castWidth (Zeros (n := VL))))
            (pure loop_vars_1))
          let vec : Int := (vec +i vstride)
          (pure (vec))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: VL : Nat, ngrp : Nat, nvec : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nvec = 4 ∧ ngrp = 2 ∧ (is_VL VL) -/
def execute_ZERO_ZA4_RI_2 (VL : Nat) (ngrp : Nat) (nvec : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name ngrp)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let vec : Int := (vec -i (fmod_int vec nvec))
  let vec ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((ngrp -i 1)))
    (do
      let mut loop_vars := vec
      for r in [loop_r_lower:loop_r_upper:1]i do
        let vec := loop_vars
        loop_vars ← do
          let vec : Int := vec
          let loop_i_lower : Nat := 0
          let loop_i_upper : Nat := (Sail.Int.toNatChecked ((nvec -i 1)))
          (do
            let mut loop_vars_1 := ()
            for i in [loop_i_lower:loop_i_upper:1]i do
              let () := loop_vars_1
              loop_vars_1 ← do
                (ZAvector_set (vec +i i) VL (Sail.BitVec.castWidth (Zeros (n := VL))))
            (pure loop_vars_1))
          let vec : Int := (vec +i vstride)
          (pure (vec))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: VL : Nat, ngrp : Nat, nvec : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nvec = 4 ∧ ngrp = 4 ∧ (is_VL VL) -/
def execute_ZERO_ZA4_RI_4 (VL : Nat) (ngrp : Nat) (nvec : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name ngrp)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let vec : Int := (vec -i (fmod_int vec nvec))
  let vec ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((ngrp -i 1)))
    (do
      let mut loop_vars := vec
      for r in [loop_r_lower:loop_r_upper:1]i do
        let vec := loop_vars
        loop_vars ← do
          let vec : Int := vec
          let loop_i_lower : Nat := 0
          let loop_i_upper : Nat := (Sail.Int.toNatChecked ((nvec -i 1)))
          (do
            let mut loop_vars_1 := ()
            for i in [loop_i_lower:loop_i_upper:1]i do
              let () := loop_vars_1
              loop_vars_1 ← do
                (ZAvector_set (vec +i i) VL (Sail.BitVec.castWidth (Zeros (n := VL))))
            (pure loop_vars_1))
          let vec : Int := (vec +i vstride)
          (pure (vec))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


def decode_LUTI2_MZ2_ZTZ_8 (i3 : (BitVec 3)) (size : (BitVec 2)) (Zn : (BitVec 5)) (D : (BitVec 1)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((size == 0b10#2) || (size == 0b11#2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let isize : Nat := 2
  let n : Int := (BitVec.toNat Zn)
  let dstride : Nat := 8
  let d : Int := (BitVec.toNat ((D +++ 0#1) +++ Zd))
  let imm : Int := (BitVec.toNat i3)
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_LUTI2_MZ2_ZTZ_8 128 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 256 =>
    (do
      (execute_LUTI2_MZ2_ZTZ_8 256 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 512 =>
    (do
      (execute_LUTI2_MZ2_ZTZ_8 512 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 1024 =>
    (do
      (execute_LUTI2_MZ2_ZTZ_8 1024 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 2048 =>
    (do
      (execute_LUTI2_MZ2_ZTZ_8 2048 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | _ => (pure (()))


def decode_LUTI4_MZ2_ZTZ_8 (i2 : (BitVec 2)) (size : (BitVec 2)) (Zn : (BitVec 5)) (D : (BitVec 1)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((size == 0b10#2) || (size == 0b11#2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let isize : Nat := 4
  let n : Int := (BitVec.toNat Zn)
  let dstride : Nat := 8
  let d : Int := (BitVec.toNat ((D +++ 0#1) +++ Zd))
  let imm : Int := (BitVec.toNat i2)
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_LUTI4_MZ2_ZTZ_8 128 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 256 =>
    (do
      (execute_LUTI4_MZ2_ZTZ_8 256 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 512 =>
    (do
      (execute_LUTI4_MZ2_ZTZ_8 512 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 1024 =>
    (do
      (execute_LUTI4_MZ2_ZTZ_8 1024 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 2048 =>
    (do
      (execute_LUTI4_MZ2_ZTZ_8 2048 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | _ => (pure (()))


def decode_LUTI2_MZ4_ZTZ_4 (i2 : (BitVec 2)) (size : (BitVec 2)) (Zn : (BitVec 5)) (D : (BitVec 1)) (Zd : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((size == 0b10#2) || (size == 0b11#2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let isize : Nat := 2
  let n : Int := (BitVec.toNat Zn)
  let dstride : Nat := 4
  let d : Int := (BitVec.toNat ((D +++ 0b00#2) +++ Zd))
  let imm : Int := (BitVec.toNat i2)
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_LUTI2_MZ4_ZTZ_4 128 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 256 =>
    (do
      (execute_LUTI2_MZ4_ZTZ_4 256 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 512 =>
    (do
      (execute_LUTI2_MZ4_ZTZ_4 512 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 1024 =>
    (do
      (execute_LUTI2_MZ4_ZTZ_4 1024 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 2048 =>
    (do
      (execute_LUTI2_MZ4_ZTZ_4 2048 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | _ => (pure (()))


def decode_LUTI4_MZ4_ZTZ_4 (i1 : (BitVec 1)) (size : (BitVec 2)) (Zn : (BitVec 5)) (D : (BitVec 1)) (Zd : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size != 0b01#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let isize : Nat := 4
  let n : Int := (BitVec.toNat Zn)
  let dstride : Nat := 4
  let d : Int := (BitVec.toNat ((D +++ 0b00#2) +++ Zd))
  let imm : Int := (BitVec.toNat i1)
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_LUTI4_MZ4_ZTZ_4 128 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 256 =>
    (do
      (execute_LUTI4_MZ4_ZTZ_4 256 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 512 =>
    (do
      (execute_LUTI4_MZ4_ZTZ_4 512 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 1024 =>
    (do
      (execute_LUTI4_MZ4_ZTZ_4 1024 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | 2048 =>
    (do
      (execute_LUTI4_MZ4_ZTZ_4 2048 (Sail.Int.toNatChecked (d)) dstride
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (imm)) isize
        (Sail.Int.toNatChecked (n)) nreg))
  | _ => (pure (()))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, offset : Nat, s : Nat, k_vertical :
  Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  0 ≤ offset ∧ offset ≤ 15 ∧ n = 0 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_Z_RZA_B (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int := (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat index) +i offset))) dim)
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (ZAslice_read n esize vertical slice_name VL))
    ) : SailM (BitVec VL) )
  (ZAslice_set n esize vertical slice_name VL (Sail.BitVec.castWidth (Zeros (n := VL))))
  (Z_set d VL (Sail.BitVec.castWidth operand))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, offset : Nat, s : Nat, k_vertical :
  Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem n [0, 1] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_Z_RZA_H (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int := (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat index) +i offset))) dim)
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (ZAslice_read n esize vertical slice_name VL))
    ) : SailM (BitVec VL) )
  (ZAslice_set n esize vertical slice_name VL (Sail.BitVec.castWidth (Zeros (n := VL))))
  (Z_set d VL (Sail.BitVec.castWidth operand))


end ArmFull.Functions
