import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0019
import ArmFull.Fn.M0041
import ArmFull.Fn.M0099
import ArmFull.Fn.M0115
import ArmFull.Fn.M0116
import ArmFull.Fn.M0124
import ArmFull.Fn.M0145
import ArmFull.Fn.M0228
import ArmFull.Fn.M0925

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

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, index : Int, m : Nat, n : Nat, regs
  : Nat, k_scalar_form : Bool, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQRDMULH_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (index : Int) (m : Nat) (n : Nat) (regs : Nat) (scalar_form : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_int_at (← occLabel 3649) ()) ) : SailM Int )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3650)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let sat ← (( do (undefined_bool_at (← occLabel 3651) ()) ) : SailM Bool )
  (CheckAdvSIMDEnabled ())
  let op2 ← (( do (undefined_int_at (← occLabel 3652) ()) ) : SailM Int )
  let round : Bool := true
  let op2 ← (( do
    if (scalar_form : Bool)
    then
      (do
        let w__0 ← (( do (D_read m) ) : SailM (BitVec 64) )
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 index esize)) ) : SailM
          (BitVec esize) )
        let op2 : Int := ((BitVec.toInt w__1) : Int)
        (pure (op2)))
    else (pure (op2)) ) : SailM Int )
  let (op1, op2, result, sat) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (op1, op2, result, sat)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (op1, op2, result, sat) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := (op1, op2, result, sat)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (op1, op2, result, sat) := loop_vars_1
              loop_vars_1 ← do
                let w__2 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
                let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 e esize)) ) : SailM
                  (BitVec esize) )
                let op1 : Int := ((BitVec.toInt w__3) : Int)
                let op2 ← (( do
                  if ((! scalar_form) : Bool)
                  then
                    (do
                      let w__4 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                      let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__4 e esize)) ) :
                        SailM (BitVec esize) )
                      let op2 : Int := ((BitVec.toInt w__5) : Int)
                      (pure (op2)))
                  else (pure (op2)) ) : SailM Int )
                let rdmulh ← (( do (RShr ((2 *i op1) *i op2) esize round) ) : SailM Int )
                let w__6 ← (( do
                  ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ rdmulh esize))
                  ) : SailM ((BitVec esize) × Bool) )
                let (tup__0, tup__1) := (w__6 : ((BitVec esize) × Bool))
                let result : (BitVec esize) := tup__0
                let sat : Bool := tup__1
                let w__7 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__8 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__7 e esize
                    (Sail.BitVec.castWidth result))) ) : SailM (BitVec 64) )
                (D_set (d +i r) w__8)
                if (sat : Bool)
                then
                  (do
                    let w__9 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
                    (FPSCR_write (_update_FPSCR_Type_QC w__9 1#1)))
                else (pure (()))
                (pure ((op1, op2, result, sat)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Int × Int × (BitVec esize) × Bool) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, index : Int, m : Nat, n : Nat, regs
  : Nat, k_scalar_form : Bool, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQRDMLAH_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (index : Int) (m : Nat) (n : Nat) (regs : Nat) (scalar_form : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_int_at (← occLabel 3661) ()) ) : SailM Int )
  let op3 ← (( do (undefined_int_at (← occLabel 3662) ()) ) : SailM Int )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3663)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let sat ← (( do (undefined_bool_at (← occLabel 3664) ()) ) : SailM Bool )
  (CheckAdvSIMDEnabled ())
  let op2 ← (( do (undefined_int_at (← occLabel 3665) ()) ) : SailM Int )
  let round : Bool := true
  let op2 ← (( do
    if (scalar_form : Bool)
    then
      (do
        let w__0 ← (( do (D_read m) ) : SailM (BitVec 64) )
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 index esize)) ) : SailM
          (BitVec esize) )
        let op2 : Int := ((BitVec.toInt w__1) : Int)
        (pure (op2)))
    else (pure (op2)) ) : SailM Int )
  let (op1, op2, op3, result, sat) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (op1, op2, op3, result, sat)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (op1, op2, op3, result, sat) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := (op1, op2, op3, result, sat)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (op1, op2, op3, result, sat) := loop_vars_1
              loop_vars_1 ← do
                let w__2 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
                let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 e esize)) ) : SailM
                  (BitVec esize) )
                let op1 : Int := ((BitVec.toInt w__3) : Int)
                let w__4 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__4 e esize)) ) : SailM
                  (BitVec esize) )
                let op3 : Int := ((Int.shiftl (BitVec.toInt w__5) esize) : Int)
                let op2 ← (( do
                  if ((! scalar_form) : Bool)
                  then
                    (do
                      let w__6 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                      let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__6 e esize)) ) :
                        SailM (BitVec esize) )
                      let op2 : Int := ((BitVec.toInt w__7) : Int)
                      (pure (op2)))
                  else (pure (op2)) ) : SailM Int )
                let rdmlah ← (( do (RShr (op3 +i (2 *i (op1 *i op2))) esize round) ) : SailM Int )
                let w__8 ← (( do
                  ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ rdmlah esize))
                  ) : SailM ((BitVec esize) × Bool) )
                let (tup__0, tup__1) := (w__8 : ((BitVec esize) × Bool))
                let result : (BitVec esize) := tup__0
                let sat : Bool := tup__1
                let w__9 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__10 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__9 e esize
                    (Sail.BitVec.castWidth result))) ) : SailM (BitVec 64) )
                (D_set (d +i r) w__10)
                if (sat : Bool)
                then
                  (do
                    let w__11 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
                    (FPSCR_write (_update_FPSCR_Type_QC w__11 1#1)))
                else (pure (()))
                (pure ((op1, op2, op3, result, sat)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Int × Int × Int × (BitVec esize) × Bool) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, index : Int, m : Nat, n : Nat, regs
  : Nat, k_scalar_form : Bool, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQRDMLSH_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (index : Int) (m : Nat) (n : Nat) (regs : Nat) (scalar_form : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do (undefined_int_at (← occLabel 3674) ()) ) : SailM Int )
  let op3 ← (( do (undefined_int_at (← occLabel 3675) ()) ) : SailM Int )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3676)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let sat ← (( do (undefined_bool_at (← occLabel 3677) ()) ) : SailM Bool )
  (CheckAdvSIMDEnabled ())
  let op2 ← (( do (undefined_int_at (← occLabel 3678) ()) ) : SailM Int )
  let round : Bool := true
  let op2 ← (( do
    if (scalar_form : Bool)
    then
      (do
        let w__0 ← (( do (D_read m) ) : SailM (BitVec 64) )
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 index esize)) ) : SailM
          (BitVec esize) )
        let op2 : Int := ((BitVec.toInt w__1) : Int)
        (pure (op2)))
    else (pure (op2)) ) : SailM Int )
  let (op1, op2, op3, result, sat) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (op1, op2, op3, result, sat)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (op1, op2, op3, result, sat) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := (op1, op2, op3, result, sat)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (op1, op2, op3, result, sat) := loop_vars_1
              loop_vars_1 ← do
                let w__2 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
                let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 e esize)) ) : SailM
                  (BitVec esize) )
                let op1 : Int := ((BitVec.toInt w__3) : Int)
                let w__4 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__4 e esize)) ) : SailM
                  (BitVec esize) )
                let op3 : Int := ((Int.shiftl (BitVec.toInt w__5) esize) : Int)
                let op2 ← (( do
                  if ((! scalar_form) : Bool)
                  then
                    (do
                      let w__6 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                      let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__6 e esize)) ) :
                        SailM (BitVec esize) )
                      let op2 : Int := ((BitVec.toInt w__7) : Int)
                      (pure (op2)))
                  else (pure (op2)) ) : SailM Int )
                let rdmlsh ← (( do (RShr (op3 -i (2 *i (op1 *i op2))) esize round) ) : SailM Int )
                let w__8 ← (( do
                  ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ rdmlsh esize))
                  ) : SailM ((BitVec esize) × Bool) )
                let (tup__0, tup__1) := (w__8 : ((BitVec esize) × Bool))
                let result : (BitVec esize) := tup__0
                let sat : Bool := tup__1
                let w__9 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__10 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__9 e esize
                    (Sail.BitVec.castWidth result))) ) : SailM (BitVec 64) )
                (D_set (d +i r) w__10)
                if (sat : Bool)
                then
                  (do
                    let w__11 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
                    (FPSCR_write (_update_FPSCR_Type_QC w__11 1#1)))
                else (pure (()))
                (pure ((op1, op2, op3, result, sat)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Int × Int × Int × (BitVec esize) × Bool) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n :
  Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQRSHL_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3687)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let sat ← (( do (undefined_bool_at (← occLabel 3688) ()) ) : SailM Bool )
  let (result, sat) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (result, sat)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, sat) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := (result, sat)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (result, sat) := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let element ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
                let w__2 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
                let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 e esize)) ) : SailM
                  (BitVec esize) )
                let shift : Int := (BitVec.toInt (Sail.BitVec.extractLsb w__3 7 0))
                let element : Int :=
                  if ((shift ≥b 0) : Bool)
                  then (_shl_int_general element shift)
                  else
                    (let shift : Int := (Neg.neg shift)
                    (_shr_int_general (element +i (_shl_int_general 1 (shift -i 1))) shift))
                let element : Int := element
                let w__4 ← (( do
                  ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ element esize
                    is_unsigned)) ) : SailM ((BitVec esize) × Bool) )
                let (tup__0, tup__1) := (w__4 : ((BitVec esize) × Bool))
                let result : (BitVec esize) := tup__0
                let sat : Bool := tup__1
                let w__5 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__6 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__5 e esize
                    (Sail.BitVec.castWidth result))) ) : SailM (BitVec 64) )
                (D_set (d +i r) w__6)
                if (sat : Bool)
                then
                  (do
                    let w__7 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
                    (FPSCR_write (_update_FPSCR_Type_QC w__7 1#1)))
                else (pure (()))
                (pure ((result, sat)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM ((BitVec esize) × Bool) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, k_dest_unsigned : Bool, elements : Nat, esize : Nat, m : Nat, shift_amount
  : Int, k_src_unsigned : Bool, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32] ∧ List.elem elements [2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQRSHRN_Op_A_txt (d__arg : Nat) (dest_unsigned : Bool) (elements : Nat) (esize : Nat) (m : Nat) (shift_amount : Int) (src_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let operand ← (( do (undefined_int_at (← occLabel 3689) ()) ) : SailM Int )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3690)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let sat ← (( do (undefined_bool_at (← occLabel 3691) ()) ) : SailM Bool )
  (CheckAdvSIMDEnabled ())
  let round : Bool := true
  let (operand, result, sat) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
    (do
      let mut loop_vars := (operand, result, sat)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (operand, result, sat) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Qin_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e (Sail.Int.toNatChecked ((2 *i esize)))))
            ) : SailM (BitVec (2 * esize)) )
          let w__2 ← (( do (asl_Int w__1 src_unsigned) ) : SailM Int )
          let operand : Int := (w__2 : Int)
          let rshrn ← (( do (RShr operand shift_amount round) ) : SailM Int )
          let w__3 ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ rshrn esize dest_unsigned))
            ) : SailM ((BitVec esize) × Bool) )
          let (tup__0, tup__1) := (w__3 : ((BitVec esize) × Bool))
          let result : (BitVec esize) := tup__0
          let sat : Bool := tup__1
          let w__4 ← (( do (D_read d) ) : SailM (BitVec 64) )
          let w__5 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set w__4 e esize (Sail.BitVec.castWidth result))) )
            : SailM (BitVec 64) )
          (D_set d w__5)
          if (sat : Bool)
          then
            (do
              let w__6 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
              (FPSCR_write (_update_FPSCR_Type_QC w__6 1#1)))
          else (pure (()))
          (pure ((operand, result, sat)))
      (pure loop_vars)) ) : SailM (Int × (BitVec esize) × Bool) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, k_dest_unsigned : Bool, elements : Nat, esize : Nat, m : Nat, regs
  : Nat, shift_amount : Int, k_src_unsigned : Bool, List.elem regs [1, 2] ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  List.elem elements [1, 2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQSHL_i_Op_A_txt (d__arg : Nat) (dest_unsigned : Bool) (elements : Nat) (esize : Nat) (m : Nat) (regs : Nat) (shift_amount : Int) (src_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let operand ← (( do (undefined_int_at (← occLabel 3694) ()) ) : SailM Int )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3695)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let sat ← (( do (undefined_bool_at (← occLabel 3696) ()) ) : SailM Bool )
  (CheckAdvSIMDEnabled ())
  let (operand, result, sat) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (operand, result, sat)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (operand, result, sat) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
          (do
            let mut loop_vars_1 := (operand, result, sat)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (operand, result, sat) := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let w__2 ← (( do (asl_Int w__1 src_unsigned) ) : SailM Int )
                let operand : Int := (w__2 : Int)
                let w__3 ← (( do
                  ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ
                    (_shl_int_general operand shift_amount) esize dest_unsigned)) ) : SailM
                  ((BitVec esize) × Bool) )
                let (tup__0, tup__1) := (w__3 : ((BitVec esize) × Bool))
                let result : (BitVec esize) := tup__0
                let sat : Bool := tup__1
                let w__4 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__5 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__4 e esize
                    (Sail.BitVec.castWidth result))) ) : SailM (BitVec 64) )
                (D_set (d +i r) w__5)
                if (sat : Bool)
                then
                  (do
                    let w__6 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
                    (FPSCR_write (_update_FPSCR_Type_QC w__6 1#1)))
                else (pure (()))
                (pure ((operand, result, sat)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Int × (BitVec esize) × Bool) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n :
  Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQSHL_r_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let operand ← (( do (undefined_int_at (← occLabel 3699) ()) ) : SailM Int )
  let shift ← (( do (undefined_int_at (← occLabel 3700) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let (operand, shift) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (operand, shift)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (operand, shift) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := (operand, shift)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (operand, shift) := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let shift : Int := ((BitVec.toInt (Sail.BitVec.extractLsb w__1 7 0)) : Int)
                let w__2 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 e esize)) ) : SailM
                  (BitVec esize) )
                let w__4 ← (( do (asl_Int w__3 is_unsigned) ) : SailM Int )
                let operand : Int := (w__4 : Int)
                let sat ← (( do (undefined_bool_at (← occLabel 3701) ()) ) : SailM Bool )
                let result ← (( do
                  ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3702)
                    (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
                let (result, sat) ← (( do
                  if ((shift ≥b 0) : Bool)
                  then
                    (do
                      let w__5 ← (( do
                        ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ
                          (_shl_int_general operand shift) esize is_unsigned)) ) : SailM
                        ((BitVec esize) × Bool) )
                      let (tup__0, tup__1) := (w__5 : ((BitVec esize) × Bool))
                      let result : (BitVec esize) := tup__0
                      let sat : Bool := tup__1
                      (pure ((result, sat))))
                  else
                    (do
                      let w__6 ← (( do
                        ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ
                          (_shr_int_general operand (Neg.neg shift)) esize is_unsigned)) ) : SailM
                        ((BitVec esize) × Bool) )
                      let (tup__0, tup__1) := (w__6 : ((BitVec esize) × Bool))
                      let result : (BitVec esize) := tup__0
                      let sat : Bool := tup__1
                      (pure ((result, sat)))) ) : SailM ((BitVec esize) × Bool) )
                let w__7 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__8 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__7 e esize
                    (Sail.BitVec.castWidth result))) ) : SailM (BitVec 64) )
                (D_set (d +i r) w__8)
                if (sat : Bool)
                then
                  (do
                    let w__9 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
                    (FPSCR_write (_update_FPSCR_Type_QC w__9 1#1)))
                else (pure (()))
                (pure ((operand, shift)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Int × Int) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, k_dest_unsigned : Bool, elements : Nat, esize : Nat, m : Nat, shift_amount
  : Int, k_src_unsigned : Bool, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32] ∧ List.elem elements [2, 4, 8] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQSHRN_Op_A_txt (d__arg : Nat) (dest_unsigned : Bool) (elements : Nat) (esize : Nat) (m : Nat) (shift_amount : Int) (src_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let operand ← (( do (undefined_int_at (← occLabel 3703) ()) ) : SailM Int )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3704)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let sat ← (( do (undefined_bool_at (← occLabel 3705) ()) ) : SailM Bool )
  (CheckAdvSIMDEnabled ())
  let (operand, result, sat) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
    (do
      let mut loop_vars := (operand, result, sat)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (operand, result, sat) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Qin_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e (Sail.Int.toNatChecked ((2 *i esize)))))
            ) : SailM (BitVec (2 * esize)) )
          let w__2 ← (( do (asl_Int w__1 src_unsigned) ) : SailM Int )
          let operand : Int := (w__2 : Int)
          let w__3 ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ
              (_shr_int_general operand shift_amount) esize dest_unsigned)) ) : SailM
            ((BitVec esize) × Bool) )
          let (tup__0, tup__1) := (w__3 : ((BitVec esize) × Bool))
          let result : (BitVec esize) := tup__0
          let sat : Bool := tup__1
          let w__4 ← (( do (D_read d) ) : SailM (BitVec 64) )
          let w__5 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set w__4 e esize (Sail.BitVec.castWidth result))) )
            : SailM (BitVec 64) )
          (D_set d w__5)
          if (sat : Bool)
          then
            (do
              let w__6 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
              (FPSCR_write (_update_FPSCR_Type_QC w__6 1#1)))
          else (pure (()))
          (pure ((operand, result, sat)))
      (pure loop_vars)) ) : SailM (Int × (BitVec esize) × Bool) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n :
  Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VQSUB_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let diff ← (( do (undefined_int_at (← occLabel 3708) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let diff ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := diff
      for r in [loop_r_lower:loop_r_upper:1]i do
        let diff := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := diff
            for e in [loop_e_lower:loop_e_upper:1]i do
              let diff := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let w__2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
                let w__3 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__3 e esize)) ) : SailM
                  (BitVec esize) )
                let w__5 ← (( do (asl_Int w__4 is_unsigned) ) : SailM Int )
                let diff : Int := ((w__2 -i w__5) : Int)
                let sat ← (( do (undefined_bool_at (← occLabel 3709) ()) ) : SailM Bool )
                let (__tup_0, __tup_1) ← (( do
                  ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SatQ diff esize
                    is_unsigned)) ) : SailM ((BitVec esize) × Bool) )
                let w__6 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__7 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__6 e esize
                    (Sail.BitVec.castWidth __tup_0))) ) : SailM (BitVec 64) )
                (D_set (d +i r) w__7)
                let sat : Bool := __tup_1
                if (sat : Bool)
                then
                  (do
                    let w__8 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
                    (FPSCR_write (_update_FPSCR_Type_QC w__8 1#1)))
                else (pure (()))
                (pure (diff))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRADDHN_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int_at (← occLabel 3710) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let round : Bool := true
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Qin_read (Int.shiftl n 1)) ) : SailM (BitVec 128) )
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e (Sail.Int.toNatChecked ((2 *i esize)))))
            ) : SailM (BitVec (2 * esize)) )
          let w__2 ← (( do (Qin_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 e (Sail.Int.toNatChecked ((2 *i esize)))))
            ) : SailM (BitVec (2 * esize)) )
          let w__4 ← (( do (RShr (BitVec.toNat (w__1 + w__3)) esize round) ) : SailM Int )
          let result : Int := (w__4 : Int)
          let w__5 ← (( do (D_read d) ) : SailM (BitVec 64) )
          let w__6 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set w__5 e esize
              (Sail.BitVec.castWidth (integer_subrange result (esize -i 1) 0)))) ) : SailM
            (BitVec 64) )
          (D_set d w__6)
          (pure (result))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


end ArmFull.Functions
