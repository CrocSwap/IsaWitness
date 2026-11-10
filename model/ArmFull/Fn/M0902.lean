import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0146
import ArmFull.Fn.M0204
import ArmFull.Fn.M0218
import ArmFull.Fn.M0840

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

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0
  ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_USDOT_ZA_ZZV_S4x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7343)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
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
          let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let sum ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                    SailM (BitVec esize) )
                  let sum ← (( do
                    let loop_i_lower : Nat := 0
                    let loop_i_upper : Nat := 3
                    (do
                      let mut loop_vars_2 := sum
                      for i in [loop_i_lower:loop_i_upper:1]i do
                        let sum := loop_vars_2
                        loop_vars_2 ← do
                          let w__0 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                              (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                            (BitVec (esize / 4)) )
                          let element1 : Int := (BitVec.toNat w__0)
                          let w__1 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i e) +i i)
                              (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                            (BitVec (esize / 4)) )
                          let element2 : Int := (BitVec.toInt w__1)
                          let sum : (BitVec esize) := (BitVec.addInt sum (element1 *i element2))
                          (pure (sum))
                      (pure loop_vars_2)) ) : SailM (BitVec esize) )
                  (Elem_set result e esize (Sail.BitVec.castWidth sum))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0
  ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SUDOT_ZA_ZZV_S4x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7344)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
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
          let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let sum ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                    SailM (BitVec esize) )
                  let sum ← (( do
                    let loop_i_lower : Nat := 0
                    let loop_i_upper : Nat := 3
                    (do
                      let mut loop_vars_2 := sum
                      for i in [loop_i_lower:loop_i_upper:1]i do
                        let sum := loop_vars_2
                        loop_vars_2 ← do
                          let w__0 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                              (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                            (BitVec (esize / 4)) )
                          let element1 : Int := (BitVec.toInt w__0)
                          let w__1 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i e) +i i)
                              (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                            (BitVec (esize / 4)) )
                          let element2 : Int := (BitVec.toNat w__1)
                          let sum : (BitVec esize) := (BitVec.addInt sum (element1 *i element2))
                          (pure (sum))
                      (pure loop_vars_2)) ) : SailM (BitVec esize) )
                  (Elem_set result e esize (Sail.BitVec.castWidth sum))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v
  : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UDOT_ZA_ZZi_S2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7345)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
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
          let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let sum ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                    SailM (BitVec esize) )
                  let segmentbase : Int :=
                    (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
                  let s : Int := (segmentbase +i index)
                  let sum ← (( do
                    let loop_i_lower : Nat := 0
                    let loop_i_upper : Nat := 3
                    (do
                      let mut loop_vars_2 := sum
                      for i in [loop_i_lower:loop_i_upper:1]i do
                        let sum := loop_vars_2
                        loop_vars_2 ← do
                          let w__0 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                              (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                            (BitVec (esize / 4)) )
                          let element1 : Int := (BitVec.toNat w__0)
                          let w__1 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i s) +i i)
                              (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                            (BitVec (esize / 4)) )
                          let element2 : Int := (BitVec.toNat w__1)
                          let sum : (BitVec esize) := (BitVec.addInt sum (element1 *i element2))
                          (pure (sum))
                      (pure loop_vars_2)) ) : SailM (BitVec esize) )
                  (Elem_set result e esize (Sail.BitVec.castWidth sum))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v
  : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SDOT_ZA_ZZi_S2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7346)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
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
          let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let sum ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                    SailM (BitVec esize) )
                  let segmentbase : Int :=
                    (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
                  let s : Int := (segmentbase +i index)
                  let sum ← (( do
                    let loop_i_lower : Nat := 0
                    let loop_i_upper : Nat := 3
                    (do
                      let mut loop_vars_2 := sum
                      for i in [loop_i_lower:loop_i_upper:1]i do
                        let sum := loop_vars_2
                        loop_vars_2 ← do
                          let w__0 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                              (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                            (BitVec (esize / 4)) )
                          let element1 : Int := (BitVec.toInt w__0)
                          let w__1 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i s) +i i)
                              (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                            (BitVec (esize / 4)) )
                          let element2 : Int := (BitVec.toInt w__1)
                          let sum : (BitVec esize) := (BitVec.addInt sum (element1 *i element2))
                          (pure (sum))
                      (pure loop_vars_2)) ) : SailM (BitVec esize) )
                  (Elem_set result e esize (Sail.BitVec.castWidth sum))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v
  : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_USDOT_ZA_ZZi_S2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7347)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
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
          let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let sum ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                    SailM (BitVec esize) )
                  let segmentbase : Int :=
                    (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
                  let s : Int := (segmentbase +i index)
                  let sum ← (( do
                    let loop_i_lower : Nat := 0
                    let loop_i_upper : Nat := 3
                    (do
                      let mut loop_vars_2 := sum
                      for i in [loop_i_lower:loop_i_upper:1]i do
                        let sum := loop_vars_2
                        loop_vars_2 ← do
                          let w__0 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                              (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                            (BitVec (esize / 4)) )
                          let element1 : Int := (BitVec.toNat w__0)
                          let w__1 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i s) +i i)
                              (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                            (BitVec (esize / 4)) )
                          let element2 : Int := (BitVec.toInt w__1)
                          let sum : (BitVec esize) := (BitVec.addInt sum (element1 *i element2))
                          (pure (sum))
                      (pure loop_vars_2)) ) : SailM (BitVec esize) )
                  (Elem_set result e esize (Sail.BitVec.castWidth sum))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v
  : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SUDOT_ZA_ZZi_S2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7348)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
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
          let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let sum ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                    SailM (BitVec esize) )
                  let segmentbase : Int :=
                    (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
                  let s : Int := (segmentbase +i index)
                  let sum ← (( do
                    let loop_i_lower : Nat := 0
                    let loop_i_upper : Nat := 3
                    (do
                      let mut loop_vars_2 := sum
                      for i in [loop_i_lower:loop_i_upper:1]i do
                        let sum := loop_vars_2
                        loop_vars_2 ← do
                          let w__0 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                              (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                            (BitVec (esize / 4)) )
                          let element1 : Int := (BitVec.toInt w__0)
                          let w__1 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i s) +i i)
                              (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                            (BitVec (esize / 4)) )
                          let element2 : Int := (BitVec.toNat w__1)
                          let sum : (BitVec esize) := (BitVec.addInt sum (element1 *i element2))
                          (pure (sum))
                      (pure loop_vars_2)) ) : SailM (BitVec esize) )
                  (Elem_set result e esize (Sail.BitVec.castWidth sum))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v
  : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_UDOT_ZA_ZZi_D2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7349)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
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
          let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let sum ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                    SailM (BitVec esize) )
                  let segmentbase : Int :=
                    (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
                  let s : Int := (segmentbase +i index)
                  let sum ← (( do
                    let loop_i_lower : Nat := 0
                    let loop_i_upper : Nat := 3
                    (do
                      let mut loop_vars_2 := sum
                      for i in [loop_i_lower:loop_i_upper:1]i do
                        let sum := loop_vars_2
                        loop_vars_2 ← do
                          let w__0 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                              (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                            (BitVec (esize / 4)) )
                          let element1 : Int := (BitVec.toNat w__0)
                          let w__1 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i s) +i i)
                              (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                            (BitVec (esize / 4)) )
                          let element2 : Int := (BitVec.toNat w__1)
                          let sum : (BitVec esize) := (BitVec.addInt sum (element1 *i element2))
                          (pure (sum))
                      (pure loop_vars_2)) ) : SailM (BitVec esize) )
                  (Elem_set result e esize (Sail.BitVec.castWidth sum))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v
  : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_SDOT_ZA_ZZi_D2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7350)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
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
          let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let sum ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                    SailM (BitVec esize) )
                  let segmentbase : Int :=
                    (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
                  let s : Int := (segmentbase +i index)
                  let sum ← (( do
                    let loop_i_lower : Nat := 0
                    let loop_i_upper : Nat := 3
                    (do
                      let mut loop_vars_2 := sum
                      for i in [loop_i_lower:loop_i_upper:1]i do
                        let sum := loop_vars_2
                        loop_vars_2 ← do
                          let w__0 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                              (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                            (BitVec (esize / 4)) )
                          let element1 : Int := (BitVec.toInt w__0)
                          let w__1 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i s) +i i)
                              (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                            (BitVec (esize / 4)) )
                          let element2 : Int := (BitVec.toInt w__1)
                          let sum : (BitVec esize) := (BitVec.addInt sum (element1 *i element2))
                          (pure (sum))
                      (pure loop_vars_2)) ) : SailM (BitVec esize) )
                  (Elem_set result e esize (Sail.BitVec.castWidth sum))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


end ArmFull.Functions
