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
import ArmFull.Fn.M0218
import ArmFull.Fn.M0840
import ArmFull.Fn.M0843
import ArmFull.Fn.M0844

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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v
  : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 4 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UMLSL_ZA_ZZi_4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7463)
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
                          let segmentbase : Int :=
                            (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
                          let s : Int := ((2 *i segmentbase) +i index)
                          let w__0 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i e) +i i)
                              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM
                            (BitVec (esize / 2)) )
                          let element1 : Int := (BitVec.toNat w__0)
                          let w__1 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s
                              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM
                            (BitVec (esize / 2)) )
                          let element2 : Int := (BitVec.toNat w__1)
                          let product : (BitVec esize) :=
                            (Sail.BitVec.castWidth (integer_subrange (element1 *i element2)
                              (esize -i 1) 0))
                          let w__2 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
                            (BitVec esize) )
                          (Elem_set result e esize (Sail.BitVec.castWidth (w__2 - product)))
                      (pure loop_vars_2)) ) : SailM (BitVec VL) )
                  (ZAvector_set (vec +i i) VL (Sail.BitVec.castWidth result))
                  (pure (result))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v
  : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 4 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLAL_ZA_ZZi_4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7464)
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
                          let segmentbase : Int :=
                            (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
                          let s : Int := ((2 *i segmentbase) +i index)
                          let w__0 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i e) +i i)
                              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM
                            (BitVec (esize / 2)) )
                          let element1 : Int := (BitVec.toInt w__0)
                          let w__1 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s
                              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM
                            (BitVec (esize / 2)) )
                          let element2 : Int := (BitVec.toInt w__1)
                          let product : (BitVec esize) :=
                            (Sail.BitVec.castWidth (integer_subrange (element1 *i element2)
                              (esize -i 1) 0))
                          let w__2 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
                            (BitVec esize) )
                          (Elem_set result e esize (Sail.BitVec.castWidth (w__2 + product)))
                      (pure loop_vars_2)) ) : SailM (BitVec VL) )
                  (ZAvector_set (vec +i i) VL (Sail.BitVec.castWidth result))
                  (pure (result))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v
  : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 4 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLSL_ZA_ZZi_4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7465)
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
                          let segmentbase : Int :=
                            (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
                          let s : Int := ((2 *i segmentbase) +i index)
                          let w__0 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i e) +i i)
                              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM
                            (BitVec (esize / 2)) )
                          let element1 : Int := (BitVec.toInt w__0)
                          let w__1 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s
                              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM
                            (BitVec (esize / 2)) )
                          let element2 : Int := (BitVec.toInt w__1)
                          let product : (BitVec esize) :=
                            (Sail.BitVec.castWidth (integer_subrange (element1 *i element2)
                              (esize -i 1) 0))
                          let w__2 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
                            (BitVec esize) )
                          (Elem_set result e esize (Sail.BitVec.castWidth (w__2 - product)))
                      (pure loop_vars_2)) ) : SailM (BitVec VL) )
                  (ZAvector_set (vec +i i) VL (Sail.BitVec.castWidth result))
                  (pure (result))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


def decode_UMAX_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let dn : Int := (BitVec.toNat (Zdn +++ 0#1))
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let nreg : Nat := 2
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_UMAX_MZ_ZZW_2x2 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 256 =>
    (do
      (execute_UMAX_MZ_ZZW_2x2 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 512 =>
    (do
      (execute_UMAX_MZ_ZZW_2x2 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 1024 =>
    (do
      (execute_UMAX_MZ_ZZW_2x2 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 2048 =>
    (do
      (execute_UMAX_MZ_ZZW_2x2 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | _ => (pure (()))


def decode_SMAX_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let dn : Int := (BitVec.toNat (Zdn +++ 0#1))
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let nreg : Nat := 2
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SMAX_MZ_ZZW_2x2 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 256 =>
    (do
      (execute_SMAX_MZ_ZZW_2x2 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 512 =>
    (do
      (execute_SMAX_MZ_ZZW_2x2 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 1024 =>
    (do
      (execute_SMAX_MZ_ZZW_2x2 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 2048 =>
    (do
      (execute_SMAX_MZ_ZZW_2x2 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | _ => (pure (()))


def decode_UMAX_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let dn : Int := (BitVec.toNat (Zdn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let nreg : Nat := 2
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_UMAX_MZ_ZZV_2x1 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 256 =>
    (do
      (execute_UMAX_MZ_ZZV_2x1 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 512 =>
    (do
      (execute_UMAX_MZ_ZZV_2x1 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 1024 =>
    (do
      (execute_UMAX_MZ_ZZV_2x1 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 2048 =>
    (do
      (execute_UMAX_MZ_ZZV_2x1 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | _ => (pure (()))


def decode_SMAX_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let dn : Int := (BitVec.toNat (Zdn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let nreg : Nat := 2
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SMAX_MZ_ZZV_2x1 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 256 =>
    (do
      (execute_SMAX_MZ_ZZV_2x1 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 512 =>
    (do
      (execute_SMAX_MZ_ZZV_2x1 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 1024 =>
    (do
      (execute_SMAX_MZ_ZZV_2x1 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 2048 =>
    (do
      (execute_SMAX_MZ_ZZV_2x1 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | _ => (pure (()))


def decode_UMAX_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let dn : Int := (BitVec.toNat (Zdn +++ 0b00#2))
  let m : Int := (BitVec.toNat (Zm +++ 0b00#2))
  let nreg : Nat := 4
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_UMAX_MZ_ZZW_4x4 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 256 =>
    (do
      (execute_UMAX_MZ_ZZW_4x4 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 512 =>
    (do
      (execute_UMAX_MZ_ZZW_4x4 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 1024 =>
    (do
      (execute_UMAX_MZ_ZZW_4x4 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 2048 =>
    (do
      (execute_UMAX_MZ_ZZW_4x4 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | _ => (pure (()))


def decode_SMAX_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let dn : Int := (BitVec.toNat (Zdn +++ 0b00#2))
  let m : Int := (BitVec.toNat (Zm +++ 0b00#2))
  let nreg : Nat := 4
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SMAX_MZ_ZZW_4x4 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 256 =>
    (do
      (execute_SMAX_MZ_ZZW_4x4 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 512 =>
    (do
      (execute_SMAX_MZ_ZZW_4x4 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 1024 =>
    (do
      (execute_SMAX_MZ_ZZW_4x4 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 2048 =>
    (do
      (execute_SMAX_MZ_ZZW_4x4 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | _ => (pure (()))


def decode_UMAX_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let dn : Int := (BitVec.toNat (Zdn +++ 0b00#2))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let nreg : Nat := 4
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_UMAX_MZ_ZZV_4x1 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 256 =>
    (do
      (execute_UMAX_MZ_ZZV_4x1 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 512 =>
    (do
      (execute_UMAX_MZ_ZZV_4x1 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 1024 =>
    (do
      (execute_UMAX_MZ_ZZV_4x1 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 2048 =>
    (do
      (execute_UMAX_MZ_ZZV_4x1 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | _ => (pure (()))


def decode_SMAX_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let dn : Int := (BitVec.toNat (Zdn +++ 0b00#2))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let nreg : Nat := 4
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SMAX_MZ_ZZV_4x1 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 256 =>
    (do
      (execute_SMAX_MZ_ZZV_4x1 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 512 =>
    (do
      (execute_SMAX_MZ_ZZV_4x1 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 1024 =>
    (do
      (execute_SMAX_MZ_ZZV_4x1 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 2048 =>
    (do
      (execute_SMAX_MZ_ZZV_4x1 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | _ => (pure (()))


def decode_UMIN_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let dn : Int := (BitVec.toNat (Zdn +++ 0#1))
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let nreg : Nat := 2
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_UMIN_MZ_ZZW_2x2 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 256 =>
    (do
      (execute_UMIN_MZ_ZZW_2x2 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 512 =>
    (do
      (execute_UMIN_MZ_ZZW_2x2 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 1024 =>
    (do
      (execute_UMIN_MZ_ZZW_2x2 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 2048 =>
    (do
      (execute_UMIN_MZ_ZZW_2x2 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | _ => (pure (()))


def decode_SMIN_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let dn : Int := (BitVec.toNat (Zdn +++ 0#1))
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let nreg : Nat := 2
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SMIN_MZ_ZZW_2x2 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 256 =>
    (do
      (execute_SMIN_MZ_ZZW_2x2 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 512 =>
    (do
      (execute_SMIN_MZ_ZZW_2x2 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 1024 =>
    (do
      (execute_SMIN_MZ_ZZW_2x2 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 2048 =>
    (do
      (execute_SMIN_MZ_ZZW_2x2 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | _ => (pure (()))


def decode_UMIN_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let dn : Int := (BitVec.toNat (Zdn +++ 0#1))
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let nreg : Nat := 2
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_UMIN_MZ_ZZV_2x1 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 256 =>
    (do
      (execute_UMIN_MZ_ZZV_2x1 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 512 =>
    (do
      (execute_UMIN_MZ_ZZV_2x1 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 1024 =>
    (do
      (execute_UMIN_MZ_ZZV_2x1 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | 2048 =>
    (do
      (execute_UMIN_MZ_ZZV_2x1 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) nreg is_unsigned))
  | _ => (pure (()))


end ArmFull.Functions
