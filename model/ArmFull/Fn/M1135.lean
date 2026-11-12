import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0145
import ArmFull.Fn.M0147
import ArmFull.Fn.M0178
import ArmFull.Fn.M0202
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0582
import ArmFull.Fn.M1071
import ArmFull.Fn.M1072
import ArmFull.Fn.M1085
import ArmFull.Fn.M1086

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

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, nreg : Nat, nreg = 4 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMINNM_MZ_ZZW_4x4 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7295)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (dn +i r) VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (m +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) )
                  : SailM (BitVec esize) )
                let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) )
                  : SailM (BitVec esize) )
                ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sme.sail:17597.53-17597.54"
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__2 ← (( do (FPMinNum element1 element2 w__1) ) : SailM (BitVec esize) )
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e esize
                    (Sail.BitVec.castWidth w__2)) ) : SailM (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (Z_set (dn +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! results (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, nreg : Nat, nreg = 4 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FMINNM_MZ_ZZV_4x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7296)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (dn +i r) VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL)
            )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) )
                  : SailM (BitVec esize) )
                let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) )
                  : SailM (BitVec esize) )
                ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sme.sail:17660.53-17660.54"
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__2 ← (( do (FPMinNum element1 element2 w__1) ) : SailM (BitVec esize) )
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e esize
                    (Sail.BitVec.castWidth w__2)) ) : SailM (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (Z_set (dn +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! results (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, nreg = 2 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCLAMP_MZ_ZZ_2 (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7297)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL)
            )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL)
            )
          let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (d +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) )
                  : SailM (BitVec esize) )
                let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) )
                  : SailM (BitVec esize) )
                let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) )
                  : SailM (BitVec esize) )
                ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sme.sail:17725.53-17725.54"
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__2 ← (( do (FPMaxNum element1 element3 w__1) ) : SailM (BitVec esize) )
                let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__4 ← (( do (FPMinNum w__2 element2 w__3) ) : SailM (BitVec esize) )
                let w__5 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e esize
                    (Sail.BitVec.castWidth w__4)) ) : SailM (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__5) : (Vector (BitVec VL) 4))
                (pure (results))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (Z_set (d +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! results (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, nreg = 4 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCLAMP_MZ_ZZ_4 (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7298)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL)
            )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL)
            )
          let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (d +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) )
                  : SailM (BitVec esize) )
                let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) )
                  : SailM (BitVec esize) )
                let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) )
                  : SailM (BitVec esize) )
                ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sme.sail:17792.53-17792.54"
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__2 ← (( do (FPMaxNum element1 element3 w__1) ) : SailM (BitVec esize) )
                let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__4 ← (( do (FPMinNum w__2 element2 w__3) ) : SailM (BitVec esize) )
                let w__5 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e esize
                    (Sail.BitVec.castWidth w__4)) ) : SailM (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__5) : (Vector (BitVec VL) 4))
                (pure (results))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (Z_set (d +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! results (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BFCVT_Z_MZ2__ (VL : Nat) (d : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7299)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i 0) VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i 1) VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (Elem_read operand1 e 32) ) : SailM (BitVec 32) )
          let element2 ← (( do (Elem_read operand2 e 32) ) : SailM (BitVec 32) )
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let res1 ← (( do (FPConvertBF__1 (k_N := 32) element1 w__0) ) : SailM (BitVec 16) )
          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let res2 ← (( do (FPConvertBF__1 (k_N := 32) element2 w__1) ) : SailM (BitVec 16) )
          let w__2 ← (( do (Elem_set result e 16 res1) ) : SailM (BitVec VL) )
          let result := (w__2 : (BitVec VL))
          (Elem_set result (elements +i e) 16 res2)
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVT_Z_MZ2__ (VL : Nat) (d : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7300)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i 0) VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i 1) VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (Elem_read operand1 e 32) ) : SailM (BitVec 32) )
          let element2 ← (( do (Elem_read operand2 e 32) ) : SailM (BitVec 32) )
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let res1 ← (( do (FPConvertSVE__1 element1 w__0 16) ) : SailM (BitVec 16) )
          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let res2 ← (( do (FPConvertSVE__1 element2 w__1 16) ) : SailM (BitVec 16) )
          let w__2 ← (( do (Elem_set result e 16 res1) ) : SailM (BitVec VL) )
          let result := (w__2 : (BitVec VL))
          (Elem_set result (elements +i e) 16 res2)
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BFCVTN_Z_MZ2__ (VL : Nat) (d : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7301)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i 0) VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i 1) VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (Elem_read operand1 e 32) ) : SailM (BitVec 32) )
          let element2 ← (( do (Elem_read operand2 e 32) ) : SailM (BitVec 32) )
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let res1 ← (( do (FPConvertBF__1 (k_N := 32) element1 w__0) ) : SailM (BitVec 16) )
          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let res2 ← (( do (FPConvertBF__1 (k_N := 32) element2 w__1) ) : SailM (BitVec 16) )
          let w__2 ← (( do (Elem_set result ((2 *i e) +i 0) 16 res1) ) : SailM (BitVec VL) )
          let result := (w__2 : (BitVec VL))
          (Elem_set result ((2 *i e) +i 1) 16 res2)
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTN_Z_MZ2__ (VL : Nat) (d : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7302)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i 0) VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i 1) VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (Elem_read operand1 e 32) ) : SailM (BitVec 32) )
          let element2 ← (( do (Elem_read operand2 e 32) ) : SailM (BitVec 32) )
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let res1 ← (( do (FPConvertSVE__1 element1 w__0 16) ) : SailM (BitVec 16) )
          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let res2 ← (( do (FPConvertSVE__1 element2 w__1 16) ) : SailM (BitVec 16) )
          let w__2 ← (( do (Elem_set result ((2 *i e) +i 0) 16 res1) ) : SailM (BitVec VL) )
          let result := (w__2 : (BitVec VL))
          (Elem_set result ((2 *i e) +i 1) 16 res2)
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


def decode_FCVTZU_MZ_Z_2 (Zn : (BitVec 4)) (U : (BitVec 1)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  let nreg : Nat := 2
  let is_unsigned : Bool := true
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 =>
    (do
      (execute_FCVTZU_MZ_Z_2 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 256 =>
    (do
      (execute_FCVTZU_MZ_Z_2 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 512 =>
    (do
      (execute_FCVTZU_MZ_Z_2 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 1024 =>
    (do
      (execute_FCVTZU_MZ_Z_2 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 2048 =>
    (do
      (execute_FCVTZU_MZ_Z_2 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | _ => (pure (()))


def decode_FCVTZU_MZ_Z_4 (Zn : (BitVec 3)) (U : (BitVec 1)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg : Nat := 4
  let is_unsigned : Bool := true
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 =>
    (do
      (execute_FCVTZU_MZ_Z_4 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 256 =>
    (do
      (execute_FCVTZU_MZ_Z_4 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 512 =>
    (do
      (execute_FCVTZU_MZ_Z_4 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 1024 =>
    (do
      (execute_FCVTZU_MZ_Z_4 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 2048 =>
    (do
      (execute_FCVTZU_MZ_Z_4 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | _ => (pure (()))


def decode_FCVTZS_MZ_Z_2 (Zn : (BitVec 4)) (U : (BitVec 1)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  let nreg : Nat := 2
  let is_unsigned : Bool := false
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 =>
    (do
      (execute_FCVTZS_MZ_Z_2 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 256 =>
    (do
      (execute_FCVTZS_MZ_Z_2 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 512 =>
    (do
      (execute_FCVTZS_MZ_Z_2 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 1024 =>
    (do
      (execute_FCVTZS_MZ_Z_2 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 2048 =>
    (do
      (execute_FCVTZS_MZ_Z_2 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | _ => (pure (()))


def decode_FCVTZS_MZ_Z_4 (Zn : (BitVec 3)) (U : (BitVec 1)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg : Nat := 4
  let is_unsigned : Bool := false
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 =>
    (do
      (execute_FCVTZS_MZ_Z_4 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 256 =>
    (do
      (execute_FCVTZS_MZ_Z_4 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 512 =>
    (do
      (execute_FCVTZS_MZ_Z_4 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 1024 =>
    (do
      (execute_FCVTZS_MZ_Z_4 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 2048 =>
    (do
      (execute_FCVTZS_MZ_Z_4 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | _ => (pure (()))


def decode_UCVTF_MZ_Z_2 (Zn : (BitVec 4)) (U : (BitVec 1)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  let nreg : Nat := 2
  let is_unsigned : Bool := true
  let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
  let rounding ← (( do (FPRoundingMode w__1) ) : SailM FPRounding )
  match VL with
  | 128 =>
    (do
      (execute_UCVTF_MZ_Z_2 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 256 =>
    (do
      (execute_UCVTF_MZ_Z_2 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 512 =>
    (do
      (execute_UCVTF_MZ_Z_2 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 1024 =>
    (do
      (execute_UCVTF_MZ_Z_2 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 2048 =>
    (do
      (execute_UCVTF_MZ_Z_2 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | _ => (pure (()))


def decode_UCVTF_MZ_Z_4 (Zn : (BitVec 3)) (U : (BitVec 1)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg : Nat := 4
  let is_unsigned : Bool := true
  let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
  let rounding ← (( do (FPRoundingMode w__1) ) : SailM FPRounding )
  match VL with
  | 128 =>
    (do
      (execute_UCVTF_MZ_Z_4 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 256 =>
    (do
      (execute_UCVTF_MZ_Z_4 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 512 =>
    (do
      (execute_UCVTF_MZ_Z_4 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 1024 =>
    (do
      (execute_UCVTF_MZ_Z_4 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 2048 =>
    (do
      (execute_UCVTF_MZ_Z_4 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | _ => (pure (()))


def decode_SCVTF_MZ_Z_2 (Zn : (BitVec 4)) (U : (BitVec 1)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  let nreg : Nat := 2
  let is_unsigned : Bool := false
  let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
  let rounding ← (( do (FPRoundingMode w__1) ) : SailM FPRounding )
  match VL with
  | 128 =>
    (do
      (execute_SCVTF_MZ_Z_2 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 256 =>
    (do
      (execute_SCVTF_MZ_Z_2 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 512 =>
    (do
      (execute_SCVTF_MZ_Z_2 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 1024 =>
    (do
      (execute_SCVTF_MZ_Z_2 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 2048 =>
    (do
      (execute_SCVTF_MZ_Z_2 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | _ => (pure (()))


end ArmFull.Functions
