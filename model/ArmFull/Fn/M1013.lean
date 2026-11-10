import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0019
import ArmFull.Fn.M0020
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0043
import ArmFull.Fn.M0047
import ArmFull.Fn.M0048
import ArmFull.Fn.M0055
import ArmFull.Fn.M0057
import ArmFull.Fn.M0063
import ArmFull.Fn.M0087
import ArmFull.Fn.M0099
import ArmFull.Fn.M0116
import ArmFull.Fn.M0124
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203
import ArmFull.Fn.M0228
import ArmFull.Fn.M0841
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

/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSUBHN_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3766)
      (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
  (CheckAdvSIMDEnabled ())
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
          let result := ((w__1 - w__3) : (BitVec (2 * esize)))
          let w__4 ← (( do (D_read d) ) : SailM (BitVec 64) )
          let w__5 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set w__4 e esize
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb result
                (Sail.Int.toNatChecked (((2 *i esize) -i 1))) esize)))) ) : SailM (BitVec 64) )
          (D_set d w__5)
          (pure (result))
      (pure loop_vars)) ) : SailM (BitVec (2 * esize)) )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, regs : Nat, List.elem
  regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSUB_i_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
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
        let loop_e_upper : Int := (elements -i 1)
        (do
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let w__0 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
              let w__1 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
              let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e esize)) ) : SailM
                (BitVec esize) )
              let w__3 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
              let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__3 e esize)) ) : SailM
                (BitVec esize) )
              let w__5 ← (( do
                ((Sail.BitVec.castWidth ) <$> (Elem_set w__0 e esize
                  (Sail.BitVec.castWidth (w__2 - w__4)))) ) : SailM (BitVec 64) )
              (D_set (d +i r) w__5)
          (pure loop_vars_1))
    (pure loop_vars))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, k_is_vsubw :
  Bool, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VSUBL_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (is_vsubw : Bool) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let result ← (( do (undefined_int_at (← occLabel 3767) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let op1 ← (( do (undefined_int_at (← occLabel 3768) ()) ) : SailM Int )
          let op1 ← (( do
            if (is_vsubw : Bool)
            then
              (do
                let w__0 ← (( do (Qin_read (Int.shiftl n 1)) ) : SailM (BitVec 128) )
                let w__1 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                (asl_Int w__1 is_unsigned))
            else
              (do
                let w__3 ← (( do (Din_read n) ) : SailM (BitVec 64) )
                let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__3 e esize)) ) : SailM
                  (BitVec esize) )
                (asl_Int w__4 is_unsigned)) ) : SailM Int )
          let op1 : Int := op1
          let w__6 ← (( do (Din_read m) ) : SailM (BitVec 64) )
          let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__6 e esize)) ) : SailM
            (BitVec esize) )
          let w__8 ← (( do (asl_Int w__7 is_unsigned) ) : SailM Int )
          let result : Int := ((op1 -i w__8) : Int)
          let w__9 ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
          let w__10 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set w__9 e (Sail.Int.toNatChecked ((2 *i esize)))
              (Sail.BitVec.castWidth (integer_subrange result ((2 *i esize) -i 1) 0)))) ) : SailM
            (BitVec 128) )
          (Q_set (Int.shiftr d 1) w__10)
          (pure (result))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VSWP_Op_A_txt (d : Nat) (m : Nat) (regs : Nat) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        if ((d == m) : Bool)
        then
          (do
            let w__0 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
            (D_set (d +i r) w__0))
        else
          (do
            let w__1 ← (( do (Din_read (m +i r)) ) : SailM (BitVec 64) )
            (D_set (d +i r) w__1)
            let w__2 ← (( do (Din_read (d +i r)) ) : SailM (BitVec 64) )
            (D_set (m +i r) w__2))
    (pure loop_vars))


/-- Type quantifiers: d__arg : Nat, k_is_vtbl : Bool, length : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem length [1, 2, 3, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VTBL_Op_A_txt (d__arg : Nat) (is_vtbl : Bool) (length : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let d : Int := d__arg
  let index ← (( do (undefined_int_at (← occLabel 3769) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let table3 ← (( do
    if ((length == 4) : Bool)
    then
      (do
        (D_read (n +i 3)))
    else (pure ((Zeros (n := 64)))) ) : SailM (BitVec 64) )
  let table2 ← (( do
    if ((length ≥b 3) : Bool)
    then
      (do
        (D_read (n +i 2)))
    else (pure ((Zeros (n := 64)))) ) : SailM (BitVec 64) )
  let table1 ← (( do
    if ((length ≥b 2) : Bool)
    then
      (do
        (D_read (n +i 1)))
    else (pure ((Zeros (n := 64)))) ) : SailM (BitVec 64) )
  let w__3 ← (( do (D_read n) ) : SailM (BitVec 64) )
  let table : (BitVec 256) := (((table3 +++ table2) +++ table1) +++ w__3)
  let index ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := 7
    (do
      let mut loop_vars := index
      for i in [loop_i_lower:loop_i_upper:1]i do
        let index := loop_vars
        loop_vars ← do
          let w__4 ← (( do (D_read m) ) : SailM (BitVec 64) )
          let w__5 ← (( do (Elem_read w__4 i 8) ) : SailM (BitVec 8) )
          let index : Int := ((BitVec.toNat w__5) : Int)
          let index : Int := index
          if ((index <b (8 *i length)) : Bool)
          then
            (do
              let w__6 ← (( do (D_read d) ) : SailM (BitVec 64) )
              let w__7 ← (( do (Elem_read table index 8) ) : SailM (BitVec 8) )
              let w__8 ← (( do (Elem_set w__6 i 8 w__7) ) : SailM (BitVec 64) )
              (D_set d w__8))
          else
            (do
              if (is_vtbl : Bool)
              then
                (do
                  let w__9 ← (( do (D_read d) ) : SailM (BitVec 64) )
                  let w__10 ← (( do (Elem_set w__9 i 8 (Zeros (n := 8))) ) : SailM (BitVec 64) )
                  (D_set d w__10))
              else (pure (())))
          (pure (index))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m__arg : Nat, regs : Nat, List.elem
  regs [1, 2] ∧
  0 ≤ m__arg ∧
  m__arg ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VTRN_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m__arg : Nat) (regs : Nat) : SailM Unit := do
  let d : Int := d__arg
  let m : Int := m__arg
  (CheckAdvSIMDEnabled ())
  let h : Int := (fdiv_int elements 2)
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        if ((d == m) : Bool)
        then
          (do
            let w__0 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
            (D_set (d +i r) w__0))
        else
          (do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (h -i 1)
            (do
              let mut loop_vars_1 := ()
              for e in [loop_e_lower:loop_e_upper:1]i do
                let () := loop_vars_1
                loop_vars_1 ← do
                  let w__1 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                  let w__2 ← (( do (Din_read (m +i r)) ) : SailM (BitVec 64) )
                  let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 (2 *i e) esize))
                    ) : SailM (BitVec esize) )
                  let w__4 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_set w__1 ((2 *i e) +i 1) esize
                      (Sail.BitVec.castWidth w__3))) ) : SailM (BitVec 64) )
                  (D_set (d +i r) w__4)
                  let w__5 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                  let w__6 ← (( do (Din_read (d +i r)) ) : SailM (BitVec 64) )
                  let w__7 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read w__6 ((2 *i e) +i 1) esize)) ) : SailM
                    (BitVec esize) )
                  let w__8 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_set w__5 (2 *i e) esize
                      (Sail.BitVec.castWidth w__7))) ) : SailM (BitVec 64) )
                  (D_set (m +i r) w__8)
              (pure loop_vars_1)))
    (pure loop_vars))


/-- Type quantifiers: d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, regs : Nat, List.elem
  regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VTST_Op_A_txt (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
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
        let loop_e_upper : Int := (elements -i 1)
        (do
          let mut loop_vars_1 := ()
          for e in [loop_e_lower:loop_e_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let w__0 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
              let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) : SailM
                (BitVec esize) )
              let w__2 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
              let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 e esize)) ) : SailM
                (BitVec esize) )
              if ((! (IsZero (w__1 &&& w__3))) : Bool)
              then
                (do
                  let w__4 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                  let w__5 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_set w__4 e esize
                      (Sail.BitVec.castWidth (Ones (n := esize))))) ) : SailM (BitVec 64) )
                  (D_set (d +i r) w__5))
              else
                (do
                  let w__6 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                  let w__7 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_set w__6 e esize
                      (Sail.BitVec.castWidth (Zeros (n := esize))))) ) : SailM (BitVec 64) )
                  (D_set (d +i r) w__7))
          (pure loop_vars_1))
    (pure loop_vars))


/-- Type quantifiers: d__arg : Nat, esize : Nat, m__arg : Nat, k_quadword_operation : Bool, 0 ≤
  m__arg ∧ m__arg ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VUZP_Op_A_txt (d__arg : Nat) (esize : Nat) (m__arg : Nat) (quadword_operation : Bool) : SailM Unit := do
  let d : Int := d__arg
  let m : Int := m__arg
  let zipped_d ← (( do (undefined_bitvector_at (← occLabel 3770) 128) ) : SailM (BitVec 128) )
  let zipped_q ← (( do (undefined_bitvector_at (← occLabel 3771) 256) ) : SailM (BitVec 256) )
  (CheckAdvSIMDEnabled ())
  if (quadword_operation : Bool)
  then
    (do
      if ((d == m) : Bool)
      then
        (do
          let w__0 ← (( do (__UNKNOWN_bits 128) ) : SailM (BitVec 128) )
          (Q_set (Int.shiftr d 1) w__0))
      else
        (do
          let w__1 ← (( do (Q_read (Int.shiftr m 1)) ) : SailM (BitVec 128) )
          let w__2 ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
          let zipped_q : (BitVec 256) := (w__1 +++ w__2)
          let loop_e_lower : Nat := 0
          let loop_e_upper : Nat := (Sail.Int.toNatChecked (((Int.ediv 128 esize) -i 1)))
          (do
            let mut loop_vars := ()
            for e in [loop_e_lower:loop_e_upper:1]i do
              let () := loop_vars
              loop_vars ← do
                let w__3 ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
                let w__4 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read zipped_q (2 *i e) esize)) ) : SailM
                  (BitVec esize) )
                let w__5 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__3 e esize (Sail.BitVec.castWidth w__4)))
                  ) : SailM (BitVec 128) )
                (Q_set (Int.shiftr d 1) w__5)
                let w__6 ← (( do (Q_read (Int.shiftr m 1)) ) : SailM (BitVec 128) )
                let w__7 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read zipped_q ((2 *i e) +i 1) esize)) ) :
                  SailM (BitVec esize) )
                let w__8 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__6 e esize (Sail.BitVec.castWidth w__7)))
                  ) : SailM (BitVec 128) )
                (Q_set (Int.shiftr m 1) w__8)
            (pure loop_vars))))
  else
    (do
      if ((d == m) : Bool)
      then
        (do
          let w__9 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
          (D_set d w__9))
      else
        (do
          let w__10 ← (( do (D_read m) ) : SailM (BitVec 64) )
          let w__11 ← (( do (D_read d) ) : SailM (BitVec 64) )
          let zipped_d : (BitVec 128) := (w__10 +++ w__11)
          let loop_e_lower : Nat := 0
          let loop_e_upper : Nat := (Sail.Int.toNatChecked (((Int.ediv 64 esize) -i 1)))
          (do
            let mut loop_vars := ()
            for e in [loop_e_lower:loop_e_upper:1]i do
              let () := loop_vars
              loop_vars ← do
                let w__12 ← (( do (D_read d) ) : SailM (BitVec 64) )
                let w__13 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read zipped_d (2 *i e) esize)) ) : SailM
                  (BitVec esize) )
                let w__14 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__12 e esize
                    (Sail.BitVec.castWidth w__13))) ) : SailM (BitVec 64) )
                (D_set d w__14)
                let w__15 ← (( do (D_read m) ) : SailM (BitVec 64) )
                let w__16 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read zipped_d ((2 *i e) +i 1) esize)) ) :
                  SailM (BitVec esize) )
                let w__17 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__15 e esize
                    (Sail.BitVec.castWidth w__16))) ) : SailM (BitVec 64) )
                (D_set m w__17)
            (pure loop_vars))))


/-- Type quantifiers: d : Nat, esize : Nat, m : Nat, k_quadword_operation : Bool, 0 ≤ m ∧
  m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VZIP_Op_A_txt (d : Nat) (esize : Nat) (m : Nat) (quadword_operation : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  if (quadword_operation : Bool)
  then
    (do
      if ((d == m) : Bool)
      then
        (do
          let w__0 ← (( do (__UNKNOWN_bits 128) ) : SailM (BitVec 128) )
          (Q_set (Int.shiftl d 1) w__0))
      else
        (do
          let zipped_q ← (( do (undefined_bitvector_at (← occLabel 3773) 256) ) : SailM
            (BitVec 256) )
          let zipped_q ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Nat := (Sail.Int.toNatChecked (((Int.ediv 128 esize) -i 1)))
            (do
              let mut loop_vars := zipped_q
              for e in [loop_e_lower:loop_e_upper:1]i do
                let zipped_q := loop_vars
                loop_vars ← do
                  let w__1 ← (( do (Q_read (Int.shiftl d 1)) ) : SailM (BitVec 128) )
                  let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e esize)) ) :
                    SailM (BitVec esize) )
                  let w__3 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_set zipped_q (2 *i e) esize
                      (Sail.BitVec.castWidth w__2))) ) : SailM (BitVec 256) )
                  let zipped_q := (w__3 : (BitVec 256))
                  let w__4 ← (( do (Q_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
                  let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__4 e esize)) ) :
                    SailM (BitVec esize) )
                  ((Sail.BitVec.castWidth ) <$> (Elem_set zipped_q ((2 *i e) +i 1) esize
                    (Sail.BitVec.castWidth w__5)))
              (pure loop_vars)) ) : SailM (BitVec 256) )
          (Q_set (Int.shiftl d 1) (Sail.BitVec.extractLsb zipped_q 127 0))
          (Q_set (Int.shiftl m 1) (Sail.BitVec.extractLsb zipped_q 255 128))))
  else
    (do
      if ((d == m) : Bool)
      then
        (do
          let w__7 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
          (D_set d w__7))
      else
        (do
          let zipped_d ← (( do (undefined_bitvector_at (← occLabel 3772) 128) ) : SailM
            (BitVec 128) )
          let zipped_d ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Nat := (Sail.Int.toNatChecked (((Int.ediv 64 esize) -i 1)))
            (do
              let mut loop_vars := zipped_d
              for e in [loop_e_lower:loop_e_upper:1]i do
                let zipped_d := loop_vars
                loop_vars ← do
                  let w__8 ← (( do (D_read d) ) : SailM (BitVec 64) )
                  let w__9 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__8 e esize)) ) :
                    SailM (BitVec esize) )
                  let w__10 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_set zipped_d (2 *i e) esize
                      (Sail.BitVec.castWidth w__9))) ) : SailM (BitVec 128) )
                  let zipped_d := (w__10 : (BitVec 128))
                  let w__11 ← (( do (D_read m) ) : SailM (BitVec 64) )
                  let w__12 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__11 e esize)) ) :
                    SailM (BitVec esize) )
                  ((Sail.BitVec.castWidth ) <$> (Elem_set zipped_d ((2 *i e) +i 1) esize
                    (Sail.BitVec.castWidth w__12)))
              (pure loop_vars)) ) : SailM (BitVec 128) )
          (D_set d (Sail.BitVec.extractLsb zipped_d 63 0))
          (D_set m (Sail.BitVec.extractLsb zipped_d 127 64))))


/-- Type quantifiers: t : Nat, 0 ≤ t ∧ t ≤ 15 -/
def execute_aarch32_instrs_VMRS_Op_AS_txt (reg : (BitVec 4)) (t : Nat) : SailM Unit := do
  if ((reg == 0b0001#4) : Bool)
  then
    (do
      (CheckVFPEnabled true)
      if ((t == 15) : Bool)
      then
        (do
          let w__0 ← (( do readReg FPSR ) : SailM (BitVec 64) )
          let w__1 ← (( do readReg FPSR ) : SailM (BitVec 64) )
          let w__2 ← (( do readReg FPSR ) : SailM (BitVec 64) )
          let w__3 ← (( do readReg FPSR ) : SailM (BitVec 64) )
          let split_vec :=
            ((_get_FPSR_Type_N w__0) +++ ((_get_FPSR_Type_Z w__1) +++ ((_get_FPSR_Type_C w__2) +++ (_get_FPSR_Type_V
                    w__3))))
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__4 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
          let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__5 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
          let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__6 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
          let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__7 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
      else
        (do
          let w__8 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
          (R_set t w__8)))
  else
    (do
      let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__9.EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          (CheckVFPEnabled false)
          (AArch32_CheckAdvSIMDOrFPRegisterTraps reg)
          match reg with
          | 0b0000 =>
            (do
              let w__10 ← (( do readReg FPSID ) : SailM (BitVec 32) )
              (R_set t w__10))
          | 0b0101 =>
            (do
              let w__11 ← (( do (MVFR2_read ()) ) : SailM (BitVec 32) )
              (R_set t w__11))
          | 0b0110 =>
            (do
              let w__12 ← (( do (MVFR1_read ()) ) : SailM (BitVec 32) )
              (R_set t w__12))
          | 0b0111 =>
            (do
              let w__13 ← (( do (MVFR0_read ()) ) : SailM (BitVec 32) )
              (R_set t w__13))
          | 0b1000 =>
            (do
              let w__14 ← (( do (FPEXC_read ()) ) : SailM (BitVec 32) )
              (R_set t w__14))
          | _ =>
            (do
              (Unreachable ()))))


/-- Type quantifiers: t : Nat, 0 ≤ t ∧ t ≤ 15 -/
def execute_aarch32_instrs_VMSR_Op_AS_txt (reg : (BitVec 4)) (t : Nat) : SailM Unit := do
  if ((reg == 0b0001#4) : Bool)
  then
    (do
      (CheckVFPEnabled true)
      let w__0 ← (( do (R_read t) ) : SailM (BitVec 32) )
      (FPSCR_write (Mk_FPSCR_Type w__0)))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__1.EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          (CheckVFPEnabled false)
          match reg with
          | 0b0000 => (pure (()))
          | 0b1000 =>
            (do
              let w__2 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (FPEXC_write (Mk_FPEXC_Type w__2)))
          | _ =>
            (do
              (Unreachable ()))))


/-- Type quantifiers: d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VSEL_Op_A_txt (cond : (BitVec 4)) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckVFPEnabled true)
  match esize with
  | 16 =>
    (do
      let w__0 ← (( do (ConditionHolds cond) ) : SailM Bool )
      let w__3 ← (( do
        if (w__0 : Bool)
        then
          (do
            (S_read n))
        else
          (do
            (S_read m)) ) : SailM (BitVec 32) )
      (S_set d ((Zeros (n := 16)) +++ (Sail.BitVec.extractLsb w__3 15 0))))
  | 32 =>
    (do
      let w__4 ← (( do (ConditionHolds cond) ) : SailM Bool )
      let w__7 ← (( do
        if (w__4 : Bool)
        then
          (do
            (S_read n))
        else
          (do
            (S_read m)) ) : SailM (BitVec 32) )
      (S_set d w__7))
  | 64 =>
    (do
      let w__8 ← (( do (ConditionHolds cond) ) : SailM Bool )
      let w__11 ← (( do
        if (w__8 : Bool)
        then
          (do
            (D_read n))
        else
          (do
            (D_read m)) ) : SailM (BitVec 64) )
      (D_set d w__11))
  | _ => (pure (()))


/-- Type quantifiers: d : Nat, esize : Nat, k_is_signed : Bool, m : Nat, n : Nat, regs : Nat, List.elem
  regs [1, 2] ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VDOT_Op_A_txt (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (regs : Nat) (is_signed : Bool) : SailM Unit := do
  let operand1 ← (( do (undefined_bitvector_at (← occLabel 3843) 64) ) : SailM (BitVec 64) )
  let operand2 ← (( do (undefined_bitvector_at (← occLabel 3844) 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3845) 64) ) : SailM (BitVec 64) )
  (CheckAdvSIMDEnabled ())
  let (operand1, operand2, result) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (operand1, operand2, result)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (operand1, operand2, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
          let operand1 := (w__0 : (BitVec 64))
          let w__1 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
          let operand2 := (w__1 : (BitVec 64))
          let w__2 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
          let result := (w__2 : (BitVec 64))
          let element1 ← (( do (undefined_int_at (← occLabel 3846) ()) ) : SailM Int )
          let element2 ← (( do (undefined_int_at (← occLabel 3847) ()) ) : SailM Int )
          let (element1, element2, result) ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Nat := 1
            (do
              let mut loop_vars_1 := (element1, element2, result)
              for e in [loop_e_lower:loop_e_upper:1]i do
                let (element1, element2, result) := loop_vars_1
                loop_vars_1 ← do
                  let res : Int := 0
                  let (element1, element2, res) ← (( do
                    let loop_i_lower : Nat := 0
                    let loop_i_upper : Nat := 3
                    (do
                      let mut loop_vars_2 := (element1, element2, res)
                      for i in [loop_i_lower:loop_i_upper:1]i do
                        let (element1, element2, res) := loop_vars_2
                        loop_vars_2 ← do
                          let (element1, element2) ← (( do
                            if (is_signed : Bool)
                            then
                              (do
                                let w__3 ← (( do
                                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                                    (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                                  (BitVec (esize / 4)) )
                                let element1 : Int := ((BitVec.toInt w__3) : Int)
                                let w__4 ← (( do
                                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i e) +i i)
                                    (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                                  (BitVec (esize / 4)) )
                                let element2 : Int := ((BitVec.toInt w__4) : Int)
                                (pure ((element1, element2))))
                            else
                              (do
                                let w__5 ← (( do
                                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                                    (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                                  (BitVec (esize / 4)) )
                                let element1 : Int := ((BitVec.toNat w__5) : Int)
                                let w__6 ← (( do
                                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((4 *i e) +i i)
                                    (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                                  (BitVec (esize / 4)) )
                                let element2 : Int := ((BitVec.toNat w__6) : Int)
                                (pure ((element1, element2)))) ) : SailM (Int × Int) )
                          let res : Int := (res +i (element1 *i element2))
                          (pure ((element1, element2, res)))
                      (pure loop_vars_2)) ) : SailM (Int × Int × Int) )
                  let res : Int := res
                  let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read result e esize)) ) :
                    SailM (BitVec esize) )
                  let w__8 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
                      (Sail.BitVec.castWidth (BitVec.addInt w__7 res)))) ) : SailM (BitVec 64) )
                  let result := (w__8 : (BitVec 64))
                  (pure ((element1, element2, result)))
              (pure loop_vars_1)) ) : SailM (Int × Int × (BitVec 64)) )
          (D_set (d +i r) result)
          (pure ((operand1, operand2, result)))
      (pure loop_vars)) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec 64)) )
  (pure (()))


end ArmFull.Functions
