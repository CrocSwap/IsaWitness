module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0194
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0256
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0605
public import ArmFull.Fn.M0866 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UZP_MZ_Z_4Q (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  if ((VL <b (esize *i 4)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let quads : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((esize *i 4))))))
  let result0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7542)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7543)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7544)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result3 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7545)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let (result0, result1, result2, result3) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := 3
    (do
      let mut loop_vars := (result0, result1, result2, result3)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result0, result1, result2, result3) := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let base : Int := (r *i quads)
          let loop_q_lower : Nat := 0
          let loop_q_upper : Int := (quads -i 1)
          (do
            let mut loop_vars_1 := (result0, result1, result2, result3)
            for q in [loop_q_lower:loop_q_upper:1]i do
              let (result0, result1, result2, result3) := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand ((4 *i q) +i 0) esize)) ) : SailM
                  (BitVec esize) )
                let w__1 ← (( do (Elem_set result0 (base +i q) esize (Sail.BitVec.castWidth w__0))
                  ) : SailM (BitVec VL) )
                let result0 := (w__1 : (BitVec VL))
                let w__2 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand ((4 *i q) +i 1) esize)) ) : SailM
                  (BitVec esize) )
                let w__3 ← (( do (Elem_set result1 (base +i q) esize (Sail.BitVec.castWidth w__2))
                  ) : SailM (BitVec VL) )
                let result1 := (w__3 : (BitVec VL))
                let w__4 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand ((4 *i q) +i 2) esize)) ) : SailM
                  (BitVec esize) )
                let w__5 ← (( do (Elem_set result2 (base +i q) esize (Sail.BitVec.castWidth w__4))
                  ) : SailM (BitVec VL) )
                let result2 := (w__5 : (BitVec VL))
                let w__6 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand ((4 *i q) +i 3) esize)) ) : SailM
                  (BitVec esize) )
                let w__7 ← (( do (Elem_set result3 (base +i q) esize (Sail.BitVec.castWidth w__6))
                  ) : SailM (BitVec VL) )
                let result3 := (w__7 : (BitVec VL))
                (pure ((result0, result1, result2, result3)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM ((BitVec VL) × (BitVec VL) × (BitVec VL) × (BitVec VL)) )
  (Z_set (d +i 0) VL (Sail.BitVec.castWidth result0))
  (Z_set (d +i 1) VL (Sail.BitVec.castWidth result1))
  (Z_set (d +i 2) VL (Sail.BitVec.castWidth result2))
  (Z_set (d +i 3) VL (Sail.BitVec.castWidth result3))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, nreg =
  2 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  0 ≤ g ∧ g ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SEL_MZ_P_ZZ_2 (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7546)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let pred ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask ← (( do
    ((Sail.BitVec.castWidth ) <$> (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0)
      (Sail.Int.toNatChecked ((PL *i nreg))))) ) : SailM
    (BitVec ((Sail.Int.toNatChecked PL) * nreg)) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
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
                let w__1 ← (( do (ActivePredicateElement mask ((r *i elements) +i e) esize) ) :
                  SailM Bool )
                if (w__1 : Bool)
                then
                  (do
                    let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) )
                      : SailM (BitVec esize) )
                    let w__3 ← (( do
                      (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e esize
                        (Sail.BitVec.castWidth w__2)) ) : SailM (BitVec VL) )
                    let results :=
                      ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                    (pure (results)))
                else
                  (do
                    let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) )
                      : SailM (BitVec esize) )
                    let w__5 ← (( do
                      (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e esize
                        (Sail.BitVec.castWidth w__4)) ) : SailM (BitVec VL) )
                    let results :=
                      ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__5) : (Vector (BitVec VL) 4))
                    (pure (results)))
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


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, nreg =
  4 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  0 ≤ g ∧ g ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SEL_MZ_P_ZZ_4 (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7547)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let pred ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask ← (( do
    ((Sail.BitVec.castWidth ) <$> (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0)
      (Sail.Int.toNatChecked ((PL *i nreg))))) ) : SailM
    (BitVec ((Sail.Int.toNatChecked PL) * nreg)) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
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
                let w__1 ← (( do (ActivePredicateElement mask ((r *i elements) +i e) esize) ) :
                  SailM Bool )
                if (w__1 : Bool)
                then
                  (do
                    let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) )
                      : SailM (BitVec esize) )
                    let w__3 ← (( do
                      (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e esize
                        (Sail.BitVec.castWidth w__2)) ) : SailM (BitVec VL) )
                    let results :=
                      ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                    (pure (results)))
                else
                  (do
                    let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) )
                      : SailM (BitVec esize) )
                    let w__5 ← (( do
                      (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e esize
                        (Sail.BitVec.castWidth w__4)) ) : SailM (BitVec VL) )
                    let results :=
                      ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__5) : (Vector (BitVec VL) 4))
                    (pure (results)))
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


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Nat, isize : Nat, n : Nat, nreg : Nat, nreg
  = 1 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  isize = 2 ∧
  0 ≤ imm ∧
  imm ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_LUTI2_Z_ZTZ__ (VL : Nat) (d : Nat) (esize : Nat) (imm : Nat) (isize : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  (CheckSMEZT0Enabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let segments : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv esize (Sail.Int.toNatChecked ((isize *i nreg))))))
  let segment : Int := (Nat.mod imm segments)
  let indexes ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let table ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let base : Int := (((segment *i nreg) +i r) *i elements)
        let result ← (( do
          ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7558)
            (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := result
            for e in [loop_e_lower:loop_e_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read indexes (base +i e) isize)) ) : SailM
                  (BitVec isize) )
                let index : Int := (BitVec.toNat w__0)
                ArmFull.assert ((esize -i 1) <b 32) "sail-inputs/17-instrs64_sme.sail:35958.46-35958.47"
                let w__1 ← (( do (Elem_read table index 32) ) : SailM (BitVec 32) )
                (Elem_set result e esize
                  (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__1
                    (Sail.Int.toNatChecked ((esize -i 1))) 0)))
            (pure loop_vars_1)) ) : SailM (BitVec VL) )
        (Z_set (d +i r) VL (Sail.BitVec.castWidth result))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Nat, isize : Nat, n : Nat, nreg : Nat, nreg
  = 1 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  isize = 4 ∧
  List.elem imm [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_LUTI4_Z_ZTZ__ (VL : Nat) (d : Nat) (esize : Nat) (imm : Nat) (isize : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  (CheckSMEZT0Enabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let segments : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv esize (Sail.Int.toNatChecked ((isize *i nreg))))))
  let segment : Int := (Nat.mod imm segments)
  let indexes ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let table ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let base : Int := (((segment *i nreg) +i r) *i elements)
        let result ← (( do
          ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7559)
            (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := result
            for e in [loop_e_lower:loop_e_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read indexes (base +i e) isize)) ) : SailM
                  (BitVec isize) )
                let index : Int := (BitVec.toNat w__0)
                ArmFull.assert ((esize -i 1) <b 32) "sail-inputs/17-instrs64_sme.sail:36028.46-36028.47"
                let w__1 ← (( do (Elem_read table index 32) ) : SailM (BitVec 32) )
                (Elem_set result e esize
                  (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__1
                    (Sail.Int.toNatChecked ((esize -i 1))) 0)))
            (pure loop_vars_1)) ) : SailM (BitVec VL) )
        (Z_set (d +i r) VL (Sail.BitVec.castWidth result))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d__arg : Nat, dstride : Nat, esize : Nat, imm : Nat, isize : Nat, n
  : Nat, nreg : Nat, nreg = 2 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  isize = 2 ∧
  List.elem imm [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ dstride = 1 ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ (is_VL VL) -/
def execute_LUTI2_MZ2_ZTZ_1 (VL : Nat) (d__arg : Nat) (dstride : Nat) (esize : Nat) (imm : Nat) (isize : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckStreamingSVEEnabled ())
  (CheckSMEZT0Enabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let segments : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv esize (Sail.Int.toNatChecked ((isize *i nreg))))))
  let segment : Int := (Nat.mod imm segments)
  let indexes ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let table ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let d ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := d
      for r in [loop_r_lower:loop_r_upper:1]i do
        let d := loop_vars
        loop_vars ← do
          let base : Int := (((segment *i nreg) +i r) *i elements)
          let result ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7560)
              (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read indexes (base +i e) isize)) ) : SailM
                    (BitVec isize) )
                  let index : Int := (BitVec.toNat w__0)
                  ArmFull.assert ((esize -i 1) <b 32) "sail-inputs/17-instrs64_sme.sail:36099.46-36099.47"
                  let w__1 ← (( do (Elem_read table index 32) ) : SailM (BitVec 32) )
                  (Elem_set result e esize
                    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__1
                      (Sail.Int.toNatChecked ((esize -i 1))) 0)))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          (Z_set d VL (Sail.BitVec.castWidth result))
          let d : Int := (d +i dstride)
          (pure (d))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: VL : Nat, d__arg : Nat, dstride : Nat, esize : Nat, imm : Nat, isize : Nat, n
  : Nat, nreg : Nat, nreg = 2 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  isize = 4 ∧
  List.elem imm [0, 1, 2, 3] ∧
  List.elem esize [8, 16, 32, 64] ∧ dstride = 1 ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ (is_VL VL) -/
def execute_LUTI4_MZ2_ZTZ_1 (VL : Nat) (d__arg : Nat) (dstride : Nat) (esize : Nat) (imm : Nat) (isize : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckStreamingSVEEnabled ())
  (CheckSMEZT0Enabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let segments : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv esize (Sail.Int.toNatChecked ((isize *i nreg))))))
  let segment : Int := (Nat.mod imm segments)
  let indexes ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let table ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let d ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := d
      for r in [loop_r_lower:loop_r_upper:1]i do
        let d := loop_vars
        loop_vars ← do
          let base : Int := (((segment *i nreg) +i r) *i elements)
          let result ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7561)
              (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read indexes (base +i e) isize)) ) : SailM
                    (BitVec isize) )
                  let index : Int := (BitVec.toNat w__0)
                  ArmFull.assert ((esize -i 1) <b 32) "sail-inputs/17-instrs64_sme.sail:36172.46-36172.47"
                  let w__1 ← (( do (Elem_read table index 32) ) : SailM (BitVec 32) )
                  (Elem_set result e esize
                    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__1
                      (Sail.Int.toNatChecked ((esize -i 1))) 0)))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          (Z_set d VL (Sail.BitVec.castWidth result))
          let d : Int := (d +i dstride)
          (pure (d))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: VL : Nat, d__arg : Nat, dstride : Nat, esize : Nat, imm : Nat, isize : Nat, n
  : Nat, nreg : Nat, nreg = 4 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  isize = 2 ∧
  List.elem imm [0, 1, 2, 3] ∧
  List.elem esize [8, 16, 32, 64] ∧ dstride = 1 ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ (is_VL VL) -/
def execute_LUTI2_MZ4_ZTZ_1 (VL : Nat) (d__arg : Nat) (dstride : Nat) (esize : Nat) (imm : Nat) (isize : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckStreamingSVEEnabled ())
  (CheckSMEZT0Enabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let segments : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv esize (Sail.Int.toNatChecked ((isize *i nreg))))))
  let segment : Int := (Nat.mod imm segments)
  let indexes ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let table ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let d ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := d
      for r in [loop_r_lower:loop_r_upper:1]i do
        let d := loop_vars
        loop_vars ← do
          let base : Int := (((segment *i nreg) +i r) *i elements)
          let result ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7562)
              (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read indexes (base +i e) isize)) ) : SailM
                    (BitVec isize) )
                  let index : Int := (BitVec.toNat w__0)
                  ArmFull.assert ((esize -i 1) <b 32) "sail-inputs/17-instrs64_sme.sail:36245.46-36245.47"
                  let w__1 ← (( do (Elem_read table index 32) ) : SailM (BitVec 32) )
                  (Elem_set result e esize
                    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__1
                      (Sail.Int.toNatChecked ((esize -i 1))) 0)))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          (Z_set d VL (Sail.BitVec.castWidth result))
          let d : Int := (d +i dstride)
          (pure (d))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: VL : Nat, d__arg : Nat, dstride : Nat, esize : Nat, imm : Nat, isize : Nat, n
  : Nat, nreg : Nat, nreg = 4 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  isize = 4 ∧
  List.elem imm [0, 1] ∧
  List.elem esize [8, 16, 32, 64] ∧ dstride = 1 ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ (is_VL VL) -/
def execute_LUTI4_MZ4_ZTZ_1 (VL : Nat) (d__arg : Nat) (dstride : Nat) (esize : Nat) (imm : Nat) (isize : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckStreamingSVEEnabled ())
  (CheckSMEZT0Enabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let segments : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv esize (Sail.Int.toNatChecked ((isize *i nreg))))))
  let segment : Int := (fmod_int imm segments)
  let indexes ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let table ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let d ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := d
      for r in [loop_r_lower:loop_r_upper:1]i do
        let d := loop_vars
        loop_vars ← do
          let base : Int := (((segment *i nreg) +i r) *i elements)
          let result ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7563)
              (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read indexes (base +i e) isize)) ) : SailM
                    (BitVec isize) )
                  let index : Int := (BitVec.toNat w__0)
                  ArmFull.assert ((esize -i 1) <b 32) "sail-inputs/17-instrs64_sme.sail:36318.46-36318.47"
                  let w__1 ← (( do (Elem_read table index 32) ) : SailM (BitVec 32) )
                  (Elem_set result e esize
                    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__1
                      (Sail.Int.toNatChecked ((esize -i 1))) 0)))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          (Z_set d VL (Sail.BitVec.castWidth result))
          let d : Int := (d +i dstride)
          (pure (d))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


def decode_ZERO_ZT_I__ (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_ZERO_ZT_I__ ()))


def decode_MOVT_R_ZT__ (off3 : (BitVec 3)) (Rt : (BitVec 5)) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (Halted ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let t : Int := (BitVec.toNat Rt)
      let offset : Int := (BitVec.toNat off3)
      (__ArmCertEndOfDecode ())
      (execute_MOVT_R_ZT__ (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))))


def decode_MOVT_ZT_R__ (off3 : (BitVec 3)) (Rt : (BitVec 5)) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (Halted ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let t : Int := (BitVec.toNat Rt)
      let offset : Int := (BitVec.toNat off3)
      (__ArmCertEndOfDecode ())
      (execute_MOVT_ZT_R__ (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t))))


def decode_RDSVL_R_I__ (imm6 : (BitVec 6)) (Rd : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      let SVL ← (( do (CurrentSVL_read ()) ) : SailM Int )
      let d : Int := (BitVec.toNat Rd)
      let imm : Int := (BitVec.toInt imm6)
      match SVL with
      | 128 =>
        (do
          (execute_RDSVL_R_I__ 128 (Sail.Int.toNatChecked (d)) imm))
      | 256 =>
        (do
          (execute_RDSVL_R_I__ 256 (Sail.Int.toNatChecked (d)) imm))
      | 512 =>
        (do
          (execute_RDSVL_R_I__ 512 (Sail.Int.toNatChecked (d)) imm))
      | 1024 =>
        (do
          (execute_RDSVL_R_I__ 1024 (Sail.Int.toNatChecked (d)) imm))
      | 2048 =>
        (do
          (execute_RDSVL_R_I__ 2048 (Sail.Int.toNatChecked (d)) imm))
      | _ => (pure (())))


end ArmFull.Functions
