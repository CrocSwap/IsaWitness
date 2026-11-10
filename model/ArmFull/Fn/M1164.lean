import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0087
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0178
import ArmFull.Fn.M0202
import ArmFull.Fn.M0204
import ArmFull.Fn.M0218
import ArmFull.Fn.M0840
import ArmFull.Fn.M1002
import ArmFull.Fn.M1087
import ArmFull.Fn.M1131

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

def decode_FDOT_ZA_ZZi_4xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 3)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat off3)
  let index : Int := (BitVec.toNat i2)
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_FDOT_ZA_ZZi_4xi 128 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_FDOT_ZA_ZZi_4xi 256 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_FDOT_ZA_ZZi_4xi 512 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_FDOT_ZA_ZZi_4xi 1024 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_FDOT_ZA_ZZi_4xi 2048 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_BFVDOT_ZA_ZZi_2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 4)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat off3)
  let index : Int := (BitVec.toNat i2)
  match VL with
  | 128 =>
    (do
      (execute_BFVDOT_ZA_ZZi_2xi 128 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_BFVDOT_ZA_ZZi_2xi 256 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_BFVDOT_ZA_ZZi_2xi 512 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_BFVDOT_ZA_ZZi_2xi 1024 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_BFVDOT_ZA_ZZi_2xi 2048 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_FVDOT_ZA_ZZi_2xi (Zm : (BitVec 4)) (Rv : (BitVec 2)) (i2 : (BitVec 2)) (Zn : (BitVec 4)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat off3)
  let index : Int := (BitVec.toNat i2)
  match VL with
  | 128 =>
    (do
      (execute_FVDOT_ZA_ZZi_2xi 128 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_FVDOT_ZA_ZZi_2xi 256 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_FVDOT_ZA_ZZi_2xi 512 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_FVDOT_ZA_ZZi_2xi 1024 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_FVDOT_ZA_ZZi_2xi 2048 (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0
  ≤ v ∧
  v ≤ 31 ∧
  0 ≤ offset ∧
  offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLAL_ZA_ZZV_1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7249)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let operand1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Z_read (Nat.mod (Sail.Int.toNatChecked ((n +i r))) 32) VL))
            ) : SailM (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL)
            )
          let vec : Int := vec
          let result ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 1
            (do
              let mut loop_vars_1 := result
              for i in [loop_i_lower:loop_i_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let operand3 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (ZAvector_read (vec +i i) VL)) ) : SailM
                    (BitVec VL) )
                  let result ← (( do
                    let loop_e_lower : Nat := 0
                    let loop_e_upper : Int := (elements -i 1)
                    (do
                      let mut loop_vars_2 := result
                      for e in [loop_e_lower:loop_e_upper:1]i do
                        let result := loop_vars_2
                        loop_vars_2 ← do
                          let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM
                            (BitVec 16) )
                          let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM
                            (BitVec 16) )
                          let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                          let element1 ← (( do
                            if (sub_op : Bool)
                            then
                              (do
                                (BFNeg (k_N := 16) element1))
                            else (pure (element1)) ) : SailM (BitVec 16) )
                          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                          let w__2 ← (( do
                            (BFMulAddH_ZA (k_N := 32) element3 element1 element2 w__1) ) : SailM
                            (BitVec 32) )
                          (Elem_set result e 32 w__2)
                      (pure loop_vars_2)) ) : SailM (BitVec VL) )
                  (ZAvector_set (vec +i i) VL (Sail.BitVec.castWidth result))
                  (pure (result))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0
  ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLAL_ZA_ZZW_2x2 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7250)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (m +i r) VL)) ) : SailM
            (BitVec VL) )
          let vec : Int := vec
          let result ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 1
            (do
              let mut loop_vars_1 := result
              for i in [loop_i_lower:loop_i_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let operand3 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (ZAvector_read (vec +i i) VL)) ) : SailM
                    (BitVec VL) )
                  let result ← (( do
                    let loop_e_lower : Nat := 0
                    let loop_e_upper : Int := (elements -i 1)
                    (do
                      let mut loop_vars_2 := result
                      for e in [loop_e_lower:loop_e_upper:1]i do
                        let result := loop_vars_2
                        loop_vars_2 ← do
                          let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM
                            (BitVec 16) )
                          let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM
                            (BitVec 16) )
                          let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                          let element1 ← (( do
                            if (sub_op : Bool)
                            then
                              (do
                                (BFNeg (k_N := 16) element1))
                            else (pure (element1)) ) : SailM (BitVec 16) )
                          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                          let w__2 ← (( do
                            (BFMulAddH_ZA (k_N := 32) element3 element1 element2 w__1) ) : SailM
                            (BitVec 32) )
                          (Elem_set result e 32 w__2)
                      (pure loop_vars_2)) ) : SailM (BitVec VL) )
                  (ZAvector_set (vec +i i) VL (Sail.BitVec.castWidth result))
                  (pure (result))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0
  ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLAL_ZA_ZZV_2x1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7251)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let operand1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Z_read (Nat.mod (Sail.Int.toNatChecked ((n +i r))) 32) VL))
            ) : SailM (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL)
            )
          let vec : Int := vec
          let result ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 1
            (do
              let mut loop_vars_1 := result
              for i in [loop_i_lower:loop_i_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let operand3 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (ZAvector_read (vec +i i) VL)) ) : SailM
                    (BitVec VL) )
                  let result ← (( do
                    let loop_e_lower : Nat := 0
                    let loop_e_upper : Int := (elements -i 1)
                    (do
                      let mut loop_vars_2 := result
                      for e in [loop_e_lower:loop_e_upper:1]i do
                        let result := loop_vars_2
                        loop_vars_2 ← do
                          let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM
                            (BitVec 16) )
                          let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM
                            (BitVec 16) )
                          let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                          let element1 ← (( do
                            if (sub_op : Bool)
                            then
                              (do
                                (BFNeg (k_N := 16) element1))
                            else (pure (element1)) ) : SailM (BitVec 16) )
                          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                          let w__2 ← (( do
                            (BFMulAddH_ZA (k_N := 32) element3 element1 element2 w__1) ) : SailM
                            (BitVec 32) )
                          (Elem_set result e 32 w__2)
                      (pure loop_vars_2)) ) : SailM (BitVec VL) )
                  (ZAvector_set (vec +i i) VL (Sail.BitVec.castWidth result))
                  (pure (result))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0
  ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLAL_ZA_ZZW_4x4 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7252)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (m +i r) VL)) ) : SailM
            (BitVec VL) )
          let vec : Int := vec
          let result ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 1
            (do
              let mut loop_vars_1 := result
              for i in [loop_i_lower:loop_i_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let operand3 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (ZAvector_read (vec +i i) VL)) ) : SailM
                    (BitVec VL) )
                  let result ← (( do
                    let loop_e_lower : Nat := 0
                    let loop_e_upper : Int := (elements -i 1)
                    (do
                      let mut loop_vars_2 := result
                      for e in [loop_e_lower:loop_e_upper:1]i do
                        let result := loop_vars_2
                        loop_vars_2 ← do
                          let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM
                            (BitVec 16) )
                          let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM
                            (BitVec 16) )
                          let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                          let element1 ← (( do
                            if (sub_op : Bool)
                            then
                              (do
                                (BFNeg (k_N := 16) element1))
                            else (pure (element1)) ) : SailM (BitVec 16) )
                          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                          let w__2 ← (( do
                            (BFMulAddH_ZA (k_N := 32) element3 element1 element2 w__1) ) : SailM
                            (BitVec 32) )
                          (Elem_set result e 32 w__2)
                      (pure loop_vars_2)) ) : SailM (BitVec VL) )
                  (ZAvector_set (vec +i i) VL (Sail.BitVec.castWidth result))
                  (pure (result))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0
  ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLAL_ZA_ZZV_4x1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7253)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let operand1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Z_read (Nat.mod (Sail.Int.toNatChecked ((n +i r))) 32) VL))
            ) : SailM (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL)
            )
          let vec : Int := vec
          let result ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 1
            (do
              let mut loop_vars_1 := result
              for i in [loop_i_lower:loop_i_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let operand3 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (ZAvector_read (vec +i i) VL)) ) : SailM
                    (BitVec VL) )
                  let result ← (( do
                    let loop_e_lower : Nat := 0
                    let loop_e_upper : Int := (elements -i 1)
                    (do
                      let mut loop_vars_2 := result
                      for e in [loop_e_lower:loop_e_upper:1]i do
                        let result := loop_vars_2
                        loop_vars_2 ← do
                          let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM
                            (BitVec 16) )
                          let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM
                            (BitVec 16) )
                          let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                          let element1 ← (( do
                            if (sub_op : Bool)
                            then
                              (do
                                (BFNeg (k_N := 16) element1))
                            else (pure (element1)) ) : SailM (BitVec 16) )
                          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                          let w__2 ← (( do
                            (BFMulAddH_ZA (k_N := 32) element3 element1 element2 w__1) ) : SailM
                            (BitVec 32) )
                          (Elem_set result e 32 w__2)
                      (pure loop_vars_2)) ) : SailM (BitVec VL) )
                  (ZAvector_set (vec +i i) VL (Sail.BitVec.castWidth result))
                  (pure (result))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0
  ≤ v ∧
  v ≤ 31 ∧
  0 ≤ offset ∧
  offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLSL_ZA_ZZV_1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7254)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let operand1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Z_read (Nat.mod (Sail.Int.toNatChecked ((n +i r))) 32) VL))
            ) : SailM (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL)
            )
          let vec : Int := vec
          let result ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 1
            (do
              let mut loop_vars_1 := result
              for i in [loop_i_lower:loop_i_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let operand3 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (ZAvector_read (vec +i i) VL)) ) : SailM
                    (BitVec VL) )
                  let result ← (( do
                    let loop_e_lower : Nat := 0
                    let loop_e_upper : Int := (elements -i 1)
                    (do
                      let mut loop_vars_2 := result
                      for e in [loop_e_lower:loop_e_upper:1]i do
                        let result := loop_vars_2
                        loop_vars_2 ← do
                          let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM
                            (BitVec 16) )
                          let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM
                            (BitVec 16) )
                          let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                          let element1 ← (( do
                            if (sub_op : Bool)
                            then
                              (do
                                (BFNeg (k_N := 16) element1))
                            else (pure (element1)) ) : SailM (BitVec 16) )
                          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                          let w__2 ← (( do
                            (BFMulAddH_ZA (k_N := 32) element3 element1 element2 w__1) ) : SailM
                            (BitVec 32) )
                          (Elem_set result e 32 w__2)
                      (pure loop_vars_2)) ) : SailM (BitVec VL) )
                  (ZAvector_set (vec +i i) VL (Sail.BitVec.castWidth result))
                  (pure (result))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0
  ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLSL_ZA_ZZW_2x2 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7255)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (m +i r) VL)) ) : SailM
            (BitVec VL) )
          let vec : Int := vec
          let result ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 1
            (do
              let mut loop_vars_1 := result
              for i in [loop_i_lower:loop_i_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let operand3 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (ZAvector_read (vec +i i) VL)) ) : SailM
                    (BitVec VL) )
                  let result ← (( do
                    let loop_e_lower : Nat := 0
                    let loop_e_upper : Int := (elements -i 1)
                    (do
                      let mut loop_vars_2 := result
                      for e in [loop_e_lower:loop_e_upper:1]i do
                        let result := loop_vars_2
                        loop_vars_2 ← do
                          let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM
                            (BitVec 16) )
                          let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM
                            (BitVec 16) )
                          let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                          let element1 ← (( do
                            if (sub_op : Bool)
                            then
                              (do
                                (BFNeg (k_N := 16) element1))
                            else (pure (element1)) ) : SailM (BitVec 16) )
                          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                          let w__2 ← (( do
                            (BFMulAddH_ZA (k_N := 32) element3 element1 element2 w__1) ) : SailM
                            (BitVec 32) )
                          (Elem_set result e 32 w__2)
                      (pure loop_vars_2)) ) : SailM (BitVec VL) )
                  (ZAvector_set (vec +i i) VL (Sail.BitVec.castWidth result))
                  (pure (result))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


end ArmFull.Functions
