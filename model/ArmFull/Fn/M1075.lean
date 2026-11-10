import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0087
import ArmFull.Fn.M0124
import ArmFull.Fn.M0145
import ArmFull.Fn.M0150
import ArmFull.Fn.M0154
import ArmFull.Fn.M0175
import ArmFull.Fn.M0178
import ArmFull.Fn.M0228
import ArmFull.Fn.M0925
import ArmFull.Fn.M1040
import ArmFull.Fn.M1041
import ArmFull.Fn.M1042
import ArmFull.Fn.M1059

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

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, regs
  : Nat, k_to_integer : Bool, List.elem regs [1, 2] ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCVT_is_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (m : Nat) (regs : Nat) (to_integer : Bool) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3397)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3398)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (op1, result) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (op1, result)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (op1, result) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
          (do
            let mut loop_vars_1 := (op1, result)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (op1, result) := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let op1 := (w__1 : (BitVec esize))
                let result ← (( do
                  if (to_integer : Bool)
                  then
                    (do
                      let w__2 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                      ((Sail.BitVec.castWidth ) <$> (FPToFixed op1 0 is_unsigned w__2
                        FPRounding_ZERO esize)))
                  else
                    (do
                      let w__4 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                      ((Sail.BitVec.castWidth ) <$> (FixedToFP op1 0 is_unsigned w__4
                        FPRounding_TIEEVEN esize))) ) : SailM (BitVec esize) )
                let w__6 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__7 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__6 e esize
                    (Sail.BitVec.castWidth result))) ) : SailM (BitVec 64) )
                (D_set (d +i r) w__7)
                (pure ((op1, result)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize)) )
  (pure (()))


/-- Type quantifiers: d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, k_to_integer : Bool, 0
  ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VCVT_iv_Op_A_txt (d : Nat) (esize : Nat) (m : Nat) (rounding : FPRounding) (to_integer : Bool) (is_unsigned : Bool) : SailM Unit := do
  (CheckVFPEnabled true)
  if (to_integer : Bool)
  then
    (do
      match esize with
      | 16 =>
        (do
          let w__0 ← (( do (S_read m) ) : SailM (BitVec 32) )
          let w__1 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__2 ← (( do
            (FPToFixed (Sail.BitVec.extractLsb w__0 15 0) 0 is_unsigned w__1 rounding 32) ) : SailM
            (BitVec 32) )
          (S_set d w__2))
      | 32 =>
        (do
          let w__3 ← (( do (S_read m) ) : SailM (BitVec 32) )
          let w__4 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__5 ← (( do (FPToFixed w__3 0 is_unsigned w__4 rounding 32) ) : SailM (BitVec 32) )
          (S_set d w__5))
      | 64 =>
        (do
          let w__6 ← (( do (D_read m) ) : SailM (BitVec 64) )
          let w__7 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__8 ← (( do (FPToFixed w__6 0 is_unsigned w__7 rounding 32) ) : SailM (BitVec 32) )
          (S_set d w__8))
      | _ => (pure (())))
  else
    (do
      match esize with
      | 16 =>
        (do
          let w__9 ← (( do (S_read m) ) : SailM (BitVec 32) )
          let w__10 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let fp16 ← (( do (FixedToFP w__9 0 is_unsigned w__10 rounding 16) ) : SailM (BitVec 16)
            )
          (S_set d ((Zeros (n := 16)) +++ fp16)))
      | 32 =>
        (do
          let w__11 ← (( do (S_read m) ) : SailM (BitVec 32) )
          let w__12 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__13 ← (( do (FixedToFP w__11 0 is_unsigned w__12 rounding 32) ) : SailM
            (BitVec 32) )
          (S_set d w__13))
      | 64 =>
        (do
          let w__14 ← (( do (S_read m) ) : SailM (BitVec 32) )
          let w__15 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__16 ← (( do (FixedToFP w__14 0 is_unsigned w__15 rounding 64) ) : SailM
            (BitVec 64) )
          (D_set d w__16))
      | _ => (pure (())))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, frac_bits : Nat, k_is_unsigned :
  Bool, m : Nat, regs : Nat, k_to_fixed : Bool, List.elem regs [1, 2] ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  1 ≤ frac_bits ∧
  frac_bits ≤ 64 ∧
  List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VCVT_xs_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (frac_bits : Nat) (m : Nat) (regs : Nat) (to_fixed : Bool) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3407)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3408)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (op1, result) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (op1, result)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (op1, result) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
          (do
            let mut loop_vars_1 := (op1, result)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (op1, result) := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                  (BitVec esize) )
                let op1 := (w__1 : (BitVec esize))
                let result ← (( do
                  if (to_fixed : Bool)
                  then
                    (do
                      let w__2 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                      ((Sail.BitVec.castWidth ) <$> (FPToFixed op1 frac_bits is_unsigned w__2
                        FPRounding_ZERO esize)))
                  else
                    (do
                      let w__4 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                      ((Sail.BitVec.castWidth ) <$> (FixedToFP op1 frac_bits is_unsigned w__4
                        FPRounding_TIEEVEN esize))) ) : SailM (BitVec esize) )
                let w__6 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__7 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__6 e esize
                    (Sail.BitVec.castWidth result))) ) : SailM (BitVec 64) )
                (D_set (d +i r) w__7)
                (pure ((op1, result)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize)) )
  (pure (()))


/-- Type quantifiers: d : Nat, fp_size : Nat, frac_bits : Int, k_is_unsigned : Bool, size : Nat, k_to_fixed
  : Bool, List.elem size [16, 32] ∧ List.elem fp_size [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VCVT_xv_Op_A_txt (d : Nat) (fp_size : Nat) (frac_bits : Int) (size : Nat) (to_fixed : Bool) (is_unsigned : Bool) : SailM Unit := do
  (CheckVFPEnabled true)
  if (to_fixed : Bool)
  then
    (do
      let result ← (( do
        ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3409)
          (Sail.Int.toNatChecked (size)))) ) : SailM (BitVec size) )
      match fp_size with
      | 16 =>
        (do
          let w__0 ← (( do (S_read d) ) : SailM (BitVec 32) )
          let w__1 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let result ← (( do
            ((Sail.BitVec.castWidth ) <$> (FPToFixed (Sail.BitVec.extractLsb w__0 15 0) frac_bits
              is_unsigned w__1 FPRounding_ZERO size)) ) : SailM (BitVec size) )
          let w__2 ← (( do (Extend result 32 is_unsigned) ) : SailM (BitVec 32) )
          (S_set d w__2))
      | 32 =>
        (do
          let w__3 ← (( do (S_read d) ) : SailM (BitVec 32) )
          let w__4 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let result ← (( do
            ((Sail.BitVec.castWidth ) <$> (FPToFixed w__3 frac_bits is_unsigned w__4 FPRounding_ZERO
              size)) ) : SailM (BitVec size) )
          let w__5 ← (( do (Extend result 32 is_unsigned) ) : SailM (BitVec 32) )
          (S_set d w__5))
      | 64 =>
        (do
          let w__6 ← (( do (D_read d) ) : SailM (BitVec 64) )
          let w__7 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let result ← (( do
            ((Sail.BitVec.castWidth ) <$> (FPToFixed w__6 frac_bits is_unsigned w__7 FPRounding_ZERO
              size)) ) : SailM (BitVec size) )
          let w__8 ← (( do (Extend result 64 is_unsigned) ) : SailM (BitVec 64) )
          (D_set d w__8))
      | _ => (pure (())))
  else
    (do
      match fp_size with
      | 16 =>
        (do
          let w__9 ← (( do (S_read d) ) : SailM (BitVec 32) )
          let w__10 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let fp16 ← (( do
            (FixedToFP (Sail.BitVec.extractLsb w__9 (Sail.Int.toNatChecked ((size -i 1))) 0)
              frac_bits is_unsigned w__10 FPRounding_TIEEVEN 16) ) : SailM (BitVec 16) )
          (S_set d ((Zeros (n := 16)) +++ fp16)))
      | 32 =>
        (do
          let w__11 ← (( do (S_read d) ) : SailM (BitVec 32) )
          let w__12 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__13 ← (( do
            (FixedToFP (Sail.BitVec.extractLsb w__11 (Sail.Int.toNatChecked ((size -i 1))) 0)
              frac_bits is_unsigned w__12 FPRounding_TIEEVEN 32) ) : SailM (BitVec 32) )
          (S_set d w__13))
      | 64 =>
        (do
          let w__14 ← (( do (D_read d) ) : SailM (BitVec 64) )
          let w__15 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__16 ← (( do
            (FixedToFP (Sail.BitVec.extractLsb w__14 (Sail.Int.toNatChecked ((size -i 1))) 0)
              frac_bits is_unsigned w__15 FPRounding_TIEEVEN 64) ) : SailM (BitVec 64) )
          (D_set d w__16))
      | _ => (pure (())))


/-- Type quantifiers: k_advsimd : Bool, d__arg : Nat, elements : Int, esize : Nat, k_floating_point
  : Bool, m : Nat, regs : Int, 0 ≤ m ∧
  m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VNEG_Op_A_txt (advsimd : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (floating_point : Bool) (m : Nat) (regs : Int) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int_at (← occLabel 3548) ()) ) : SailM Int )
  (CheckAdvSIMDOrVFPEnabled true advsimd)
  if (advsimd : Bool)
  then
    (do
      let result ← (( do
        let loop_r_lower : Nat := 0
        let loop_r_upper : Int := (regs -i 1)
        (do
          let mut loop_vars := result
          for r in [loop_r_lower:loop_r_upper:1]i do
            let result := loop_vars
            loop_vars ← do
              let loop_e_lower : Nat := 0
              let loop_e_upper : Int := (elements -i 1)
              (do
                let mut loop_vars_1 := result
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let result := loop_vars_1
                  loop_vars_1 ← do
                    if (floating_point : Bool)
                    then
                      (do
                        ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:30507.61-30507.62"
                        let w__0 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                        let w__1 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                        let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e esize)) )
                          : SailM (BitVec esize) )
                        let w__3 ← (( do (FPNeg w__2) ) : SailM (BitVec esize) )
                        let w__4 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_set w__0 e esize
                            (Sail.BitVec.castWidth w__3))) ) : SailM (BitVec 64) )
                        (D_set (d +i r) w__4)
                        (pure (result)))
                    else
                      (do
                        let w__5 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                        let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__5 e esize)) )
                          : SailM (BitVec esize) )
                        let result : Int := ((Neg.neg (BitVec.toInt w__6)) : Int)
                        let w__7 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                        let w__8 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_set w__7 e esize
                            (Sail.BitVec.castWidth (integer_subrange result (esize -i 1) 0)))) ) :
                          SailM (BitVec 64) )
                        (D_set (d +i r) w__8)
                        (pure (result)))
                (pure loop_vars_1))
          (pure loop_vars)) ) : SailM Int )
      (pure (())))
  else
    (do
      match esize with
      | 16 =>
        (do
          let w__9 ← (( do (S_read m) ) : SailM (BitVec 32) )
          let w__10 ← (( do (FPNeg (Sail.BitVec.extractLsb w__9 15 0)) ) : SailM (BitVec 16) )
          (S_set d ((Zeros (n := 16)) +++ w__10)))
      | 32 =>
        (do
          let w__11 ← (( do (S_read m) ) : SailM (BitVec 32) )
          let w__12 ← (( do (FPNeg w__11) ) : SailM (BitVec 32) )
          (S_set d w__12))
      | 64 =>
        (do
          let w__13 ← (( do (D_read m) ) : SailM (BitVec 64) )
          let w__14 ← (( do (FPNeg w__13) ) : SailM (BitVec 64) )
          (D_set d w__14))
      | _ => (pure (())))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_floating_point : Bool, m : Nat, regs
  : Nat, List.elem regs [1, 2] ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRECPE_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (floating_point : Bool) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let loop_e_lower : Nat := 0
        let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
        (do
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              if (floating_point : Bool)
              then
                (do
                  let w__0 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                  let w__1 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                  let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e esize)) ) :
                    SailM (BitVec esize) )
                  let w__3 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                  let w__4 ← (( do (FPRecipEstimate w__2 w__3) ) : SailM (BitVec esize) )
                  let w__5 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_set w__0 e esize
                      (Sail.BitVec.castWidth w__4))) ) : SailM (BitVec 64) )
                  (D_set (d +i r) w__5))
              else
                (do
                  ArmFull.assert (esize == 32) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:34614.47-34614.48"
                  let w__6 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                  let w__7 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                  let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__7 e esize)) ) :
                    SailM (BitVec 32) )
                  let w__9 ← (( do (UnsignedRecipEstimate (k_N := 32) w__8) ) : SailM (BitVec 32)
                    )
                  let w__10 ← (( do (Elem_set w__6 e esize (Sail.BitVec.castWidth w__9)) ) : SailM
                    (BitVec 64) )
                  (D_set (d +i r) w__10))
          (pure loop_vars_1))
    (pure loop_vars))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_floating_point : Bool, m : Nat, regs
  : Nat, List.elem regs [1, 2] ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRSQRTE_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (floating_point : Bool) (m : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let loop_e_lower : Nat := 0
        let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
        (do
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              if (floating_point : Bool)
              then
                (do
                  let w__0 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                  let w__1 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                  let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e esize)) ) :
                    SailM (BitVec esize) )
                  let w__3 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                  let w__4 ← (( do (FPRSqrtEstimate w__2 w__3) ) : SailM (BitVec esize) )
                  let w__5 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_set w__0 e esize
                      (Sail.BitVec.castWidth w__4))) ) : SailM (BitVec 64) )
                  (D_set (d +i r) w__5))
              else
                (do
                  ArmFull.assert (esize == 32) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:35439.47-35439.48"
                  let w__6 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                  let w__7 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                  let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__7 e esize)) ) :
                    SailM (BitVec 32) )
                  let w__9 ← (( do (UnsignedRSqrtEstimate (k_N := 32) w__8) ) : SailM (BitVec 32)
                    )
                  let w__10 ← (( do (Elem_set w__6 e esize (Sail.BitVec.castWidth w__9)) ) : SailM
                    (BitVec 64) )
                  (D_set (d +i r) w__10))
          (pure loop_vars_1))
    (pure loop_vars))


def decode_aarch32_instrs_AESD_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HaveAESExt ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((size != 0b00#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_AESD_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_AESD_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__2 ← (( do (HaveAESExt ()) ) : SailM Bool )
      if ((! w__2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((size != 0b00#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_AESD_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_AESE_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HaveAESExt ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((size != 0b00#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_AESE_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_AESE_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__2 ← (( do (HaveAESExt ()) ) : SailM Bool )
      if ((! w__2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((size != 0b00#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_AESE_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_AESIMC_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HaveAESExt ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((size != 0b00#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_AESIMC_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_AESIMC_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__2 ← (( do (HaveAESExt ()) ) : SailM Bool )
      if ((! w__2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((size != 0b00#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_AESIMC_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_AESMC_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HaveAESExt ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((size != 0b00#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_AESMC_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_AESMC_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__2 ← (( do (HaveAESExt ()) ) : SailM Bool )
      if ((! w__2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((size != 0b00#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_AESMC_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_SHA1C_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HaveSHA1Ext ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if ((Q != 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let n : Int := (BitVec.toNat (N +++ Vn))
      let m : Int := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1C_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  else (pure (()))


end ArmFull.Functions
