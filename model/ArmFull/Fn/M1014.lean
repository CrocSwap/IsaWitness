import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0063
import ArmFull.Fn.M0115
import ArmFull.Fn.M0124
import ArmFull.Fn.M0181
import ArmFull.Fn.M0228
import ArmFull.Fn.M0925
import ArmFull.Fn.M0928

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

/-- Type quantifiers: d : Nat, esize : Nat, index : Nat, k_is_signed : Bool, m : Nat, n : Nat, regs
  : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VDOT_s_Op_A_txt (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (regs : Nat) (is_signed : Bool) : SailM Unit := do
  let operand1 ← (( do (undefined_bitvector_at (← occLabel 3848) 64) ) : SailM (BitVec 64) )
  let operand2 ← (( do (D_read m) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3849) 64) ) : SailM (BitVec 64) )
  (CheckAdvSIMDEnabled ())
  let (operand1, result) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (operand1, result)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (operand1, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
          let operand1 := (w__0 : (BitVec 64))
          let w__1 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
          let result := (w__1 : (BitVec 64))
          let element1 ← (( do (undefined_int_at (← occLabel 3850) ()) ) : SailM Int )
          let element2 ← (( do (undefined_int_at (← occLabel 3851) ()) ) : SailM Int )
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
                                let w__2 ← (( do
                                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                                    (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                                  (BitVec (esize / 4)) )
                                let element1 : Int := ((BitVec.toInt w__2) : Int)
                                let w__3 ← (( do
                                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2
                                    ((4 *i index) +i i) (Sail.Int.toNatChecked ((Int.ediv esize 4)))))
                                  ) : SailM (BitVec (esize / 4)) )
                                let element2 : Int := ((BitVec.toInt w__3) : Int)
                                (pure ((element1, element2))))
                            else
                              (do
                                let w__4 ← (( do
                                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((4 *i e) +i i)
                                    (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM
                                  (BitVec (esize / 4)) )
                                let element1 : Int := ((BitVec.toNat w__4) : Int)
                                let w__5 ← (( do
                                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2
                                    ((4 *i index) +i i) (Sail.Int.toNatChecked ((Int.ediv esize 4)))))
                                  ) : SailM (BitVec (esize / 4)) )
                                let element2 : Int := ((BitVec.toNat w__5) : Int)
                                (pure ((element1, element2)))) ) : SailM (Int × Int) )
                          let res : Int := (res +i (element1 *i element2))
                          (pure ((element1, element2, res)))
                      (pure loop_vars_2)) ) : SailM (Int × Int × Int) )
                  let res : Int := res
                  let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read result e esize)) ) :
                    SailM (BitVec esize) )
                  let w__7 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
                      (Sail.BitVec.castWidth (BitVec.addInt w__6 res)))) ) : SailM (BitVec 64) )
                  let result := (w__7 : (BitVec 64))
                  (pure ((element1, element2, result)))
              (pure loop_vars_1)) ) : SailM (Int × Int × (BitVec 64)) )
          (D_set (d +i r) result)
          (pure ((operand1, result)))
      (pure loop_vars)) ) : SailM ((BitVec 64) × (BitVec 64)) )
  (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VDOT_bf16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  let operand1 ← (( do (undefined_bitvector_at (← occLabel 3889) 64) ) : SailM (BitVec 64) )
  let operand2 ← (( do (undefined_bitvector_at (← occLabel 3890) 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3891) 64) ) : SailM (BitVec 64) )
  (CheckAdvSIMDEnabled ())
  let (operand1, operand2, result) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (operand1, operand2, result)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (operand1, operand2, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Din_read (n +i r)) ) : SailM (BitVec 64) )
          let operand1 := (w__0 : (BitVec 64))
          let w__1 ← (( do (Din_read (m +i r)) ) : SailM (BitVec 64) )
          let operand2 := (w__1 : (BitVec 64))
          let w__2 ← (( do (Din_read (d +i r)) ) : SailM (BitVec 64) )
          let result := (w__2 : (BitVec 64))
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Nat := 1
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16)
                    )
                  let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16)
                    )
                  let elt2_a ← (( do (Elem_read operand2 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16)
                    )
                  let elt2_b ← (( do (Elem_read operand2 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16)
                    )
                  let w__3 ← (( do (BFMulH (k_N := 16) elt1_a elt2_a) ) : SailM (BitVec (2 * 16))
                    )
                  let w__4 ← (( do (BFMulH (k_N := 16) elt1_b elt2_b) ) : SailM (BitVec (2 * 16))
                    )
                  let sum ← (( do (FPAdd_BF16 (k_N := 32) w__3 w__4) ) : SailM (BitVec 32) )
                  let w__5 ← (( do (Elem_read result e 32) ) : SailM (BitVec 32) )
                  let w__6 ← (( do (FPAdd_BF16 (k_N := 32) w__5 sum) ) : SailM (BitVec 32) )
                  (Elem_set result e 32 w__6)
              (pure loop_vars_1)) ) : SailM (BitVec 64) )
          (D_set (d +i r) result)
          (pure ((operand1, operand2, result)))
      (pure loop_vars)) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec 64)) )
  (pure (()))


/-- Type quantifiers: d : Nat, i : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem i [0, 1] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VDOT_bf16_i_Op_A_txt (d : Nat) (i : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  let operand1 ← (( do (undefined_bitvector_at (← occLabel 3892) 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3893) 64) ) : SailM (BitVec 64) )
  (CheckAdvSIMDEnabled ())
  let operand2 ← (( do (Din_read m) ) : SailM (BitVec 64) )
  let (operand1, result) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (operand1, result)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (operand1, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Din_read (n +i r)) ) : SailM (BitVec 64) )
          let operand1 := (w__0 : (BitVec 64))
          let w__1 ← (( do (Din_read (d +i r)) ) : SailM (BitVec 64) )
          let result := (w__1 : (BitVec 64))
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Nat := 1
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16)
                    )
                  let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16)
                    )
                  let elt2_a ← (( do (Elem_read operand2 ((2 *i i) +i 0) 16) ) : SailM (BitVec 16)
                    )
                  let elt2_b ← (( do (Elem_read operand2 ((2 *i i) +i 1) 16) ) : SailM (BitVec 16)
                    )
                  let w__2 ← (( do (BFMulH (k_N := 16) elt1_a elt2_a) ) : SailM (BitVec (2 * 16))
                    )
                  let w__3 ← (( do (BFMulH (k_N := 16) elt1_b elt2_b) ) : SailM (BitVec (2 * 16))
                    )
                  let sum ← (( do (FPAdd_BF16 (k_N := 32) w__2 w__3) ) : SailM (BitVec 32) )
                  let w__4 ← (( do (Elem_read result e 32) ) : SailM (BitVec 32) )
                  let w__5 ← (( do (FPAdd_BF16 (k_N := 32) w__4 sum) ) : SailM (BitVec 32) )
                  (Elem_set result e 32 w__5)
              (pure loop_vars_1)) ) : SailM (BitVec 64) )
          (D_set (d +i r) result)
          (pure ((operand1, result)))
      (pure loop_vars)) ) : SailM ((BitVec 64) × (BitVec 64)) )
  (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, 0 ≤
  n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_MMLA_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) : SailM Unit := do
  (CheckAdvSIMDEnabled ())
  let operand1 ← (( do (Q_read (Int.shiftl n 1)) ) : SailM (BitVec 128) )
  let operand2 ← (( do (Q_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
  let addend ← (( do (Q_read (Int.shiftl d 1)) ) : SailM (BitVec 128) )
  let w__0 ← (( do (MatMulAdd (k_N := 128) addend operand1 operand2 op1_unsigned op2_unsigned) ) :
    SailM (BitVec 128) )
  (Q_set (Int.shiftl d 1) w__0)


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VUSDOT_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (regs : Nat) : SailM Unit := do
  let element1 ← (( do (undefined_int_at (← occLabel 3902) ()) ) : SailM Int )
  let element2 ← (( do (undefined_int_at (← occLabel 3903) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let operand1 ← (( do (undefined_bitvector_at (← occLabel 3904) 64) ) : SailM (BitVec 64) )
  let operand2 ← (( do (undefined_bitvector_at (← occLabel 3905) 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3906) 64) ) : SailM (BitVec 64) )
  let (element1, element2, operand1, operand2, result) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (element1, element2, operand1, operand2, result)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (element1, element2, operand1, operand2, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Din_read (n +i r)) ) : SailM (BitVec 64) )
          let operand1 := (w__0 : (BitVec 64))
          let w__1 ← (( do (Din_read (m +i r)) ) : SailM (BitVec 64) )
          let operand2 := (w__1 : (BitVec 64))
          let w__2 ← (( do (Din_read (d +i r)) ) : SailM (BitVec 64) )
          let result := (w__2 : (BitVec 64))
          let (element1, element2, result) ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Nat := 1
            (do
              let mut loop_vars_1 := (element1, element2, result)
              for e in [loop_e_lower:loop_e_upper:1]i do
                let (element1, element2, result) := loop_vars_1
                loop_vars_1 ← do
                  let res ← (( do (Elem_read result e 32) ) : SailM (BitVec 32) )
                  let (element1, element2, res) ← (( do
                    let loop_b_lower : Nat := 0
                    let loop_b_upper : Nat := 3
                    (do
                      let mut loop_vars_2 := (element1, element2, res)
                      for b in [loop_b_lower:loop_b_upper:1]i do
                        let (element1, element2, res) := loop_vars_2
                        loop_vars_2 ← do
                          let w__3 ← (( do (Elem_read operand1 ((4 *i e) +i b) 8) ) : SailM
                            (BitVec 8) )
                          let element1 : Int := ((BitVec.toNat w__3) : Int)
                          let w__4 ← (( do (Elem_read operand2 ((4 *i e) +i b) 8) ) : SailM
                            (BitVec 8) )
                          let element2 : Int := ((BitVec.toInt w__4) : Int)
                          let res : (BitVec 32) := (BitVec.addInt res (element1 *i element2))
                          (pure ((element1, element2, res)))
                      (pure loop_vars_2)) ) : SailM (Int × Int × (BitVec 32)) )
                  let w__5 ← (( do (Elem_set result e 32 res) ) : SailM (BitVec 64) )
                  let result := (w__5 : (BitVec 64))
                  (pure ((element1, element2, result)))
              (pure loop_vars_1)) ) : SailM (Int × Int × (BitVec 64)) )
          (D_set (d +i r) result)
          (pure ((element1, element2, operand1, operand2, result)))
      (pure loop_vars)) ) : SailM (Int × Int × (BitVec 64) × (BitVec 64) × (BitVec 64)) )
  (pure (()))


/-- Type quantifiers: d : Nat, i : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned :
  Bool, regs : Nat, List.elem regs [1, 2] ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ List.elem i [0, 1] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_DOT_Op_A_txt (d : Nat) (i : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) (regs : Nat) : SailM Unit := do
  let element1 ← (( do (undefined_int_at (← occLabel 3907) ()) ) : SailM Int )
  let element2 ← (( do (undefined_int_at (← occLabel 3908) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let operand1 ← (( do (undefined_bitvector_at (← occLabel 3909) 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3910) 64) ) : SailM (BitVec 64) )
  let operand2 ← (( do (Din_read m) ) : SailM (BitVec 64) )
  let (element1, element2, operand1, result) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (element1, element2, operand1, result)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (element1, element2, operand1, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Din_read (n +i r)) ) : SailM (BitVec 64) )
          let operand1 := (w__0 : (BitVec 64))
          let w__1 ← (( do (Din_read (d +i r)) ) : SailM (BitVec 64) )
          let result := (w__1 : (BitVec 64))
          let (element1, element2, result) ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Nat := 1
            (do
              let mut loop_vars_1 := (element1, element2, result)
              for e in [loop_e_lower:loop_e_upper:1]i do
                let (element1, element2, result) := loop_vars_1
                loop_vars_1 ← do
                  let res ← (( do (Elem_read result e 32) ) : SailM (BitVec 32) )
                  let (element1, element2, res) ← (( do
                    let loop_b_lower : Nat := 0
                    let loop_b_upper : Nat := 3
                    (do
                      let mut loop_vars_2 := (element1, element2, res)
                      for b in [loop_b_lower:loop_b_upper:1]i do
                        let (element1, element2, res) := loop_vars_2
                        loop_vars_2 ← do
                          let w__2 ← (( do (Elem_read operand1 ((4 *i e) +i b) 8) ) : SailM
                            (BitVec 8) )
                          let w__3 ← (( do (asl_Int w__2 op1_unsigned) ) : SailM Int )
                          let element1 : Int := (w__3 : Int)
                          let w__4 ← (( do (Elem_read operand2 ((4 *i i) +i b) 8) ) : SailM
                            (BitVec 8) )
                          let w__5 ← (( do (asl_Int w__4 op2_unsigned) ) : SailM Int )
                          let element2 : Int := (w__5 : Int)
                          let res : (BitVec 32) := (BitVec.addInt res (element1 *i element2))
                          (pure ((element1, element2, res)))
                      (pure loop_vars_2)) ) : SailM (Int × Int × (BitVec 32)) )
                  let w__6 ← (( do (Elem_set result e 32 res) ) : SailM (BitVec 64) )
                  let result := (w__6 : (BitVec 64))
                  (pure ((element1, element2, result)))
              (pure loop_vars_1)) ) : SailM (Int × Int × (BitVec 64)) )
          (D_set (d +i r) result)
          (pure ((element1, element2, operand1, result)))
      (pure loop_vars)) ) : SailM (Int × Int × (BitVec 64) × (BitVec 64)) )
  (pure (()))


def decode_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size != 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let neg : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) neg)


def decode_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((size +++ Q) == 0b110#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let neg : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) neg)


def decode_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size != 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let neg : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) neg)


def decode_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((size +++ Q) == 0b110#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let neg : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)) neg)


def decode_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size != 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let sub_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op)


def decode_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let sub_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op)


def decode_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size != 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let sub_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op)


def decode_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let sub_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op)


def decode_addhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  let sub_op : Bool := (o1 == 1#1)
  let round : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow
    (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)) round
    sub_op)


def decode_raddhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  let sub_op : Bool := (o1 == 1#1)
  let round : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow
    (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)) round
    sub_op)


def decode_rsubhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  let sub_op : Bool := (o1 == 1#1)
  let round : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow
    (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)) round
    sub_op)


def decode_subhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Nat := 64
  let part : Int := (BitVec.toNat Q)
  let elements : Int := (Int.ediv datasize (Sail.Int.toNatChecked (esize)))
  let sub_op : Bool := (o1 == 1#1)
  let round : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow
    (Sail.Int.toNatChecked (d)) datasize elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (part)) round
    sub_op)


def decode_addp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_and_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 8
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let invert : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 0)])) == 1#1)
  let op : LogicalOp :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 1)])) == 1#1) : Bool)
    then LogicalOp_ORR
    else LogicalOp_AND
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) invert
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op)


def decode_bic_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 8
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let invert : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 0)])) == 1#1)
  let op : LogicalOp :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 1)])) == 1#1) : Bool)
    then LogicalOp_ORR
    else LogicalOp_AND
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) invert
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op)


def decode_orn_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 8
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let invert : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 0)])) == 1#1)
  let op : LogicalOp :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 1)])) == 1#1) : Bool)
    then LogicalOp_ORR
    else LogicalOp_AND
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) invert
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op)


def decode_orr_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 8
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let invert : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 0)])) == 1#1)
  let op : LogicalOp :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 1)])) == 1#1) : Bool)
    then LogicalOp_ORR
    else LogicalOp_AND
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) invert
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op)


end ArmFull.Functions
