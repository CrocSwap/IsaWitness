module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0015
public import ArmFull.Fn.M0063
public import ArmFull.Fn.M0099
public import ArmFull.Fn.M0124
public import ArmFull.Fn.M0148
public import ArmFull.Fn.M0149
public import ArmFull.Fn.M0172
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0227
public import ArmFull.Fn.M0957
public import ArmFull.Fn.M0958
public import ArmFull.Fn.M1092
public import ArmFull.Fn.M1122
public import ArmFull.Fn.M1126 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: k_add : Bool, k_advsimd : Bool, d__arg : Nat, elements : Int, esize : Nat, m :
  Nat, n : Nat, regs : Int, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMLA_f_Op_A_txt (add : Bool) (advsimd : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Int) : SailM Unit := do
  let d : Int := d__arg
  let addend ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3461)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let addend16 ← (( do (undefined_bitvector_at (← occLabel 3462) 16) ) : SailM (BitVec 16) )
  let addend32 ← (( do (undefined_bitvector_at (← occLabel 3463) 32) ) : SailM (BitVec 32) )
  let addend64 ← (( do (undefined_bitvector_at (← occLabel 3464) 64) ) : SailM (BitVec 64) )
  let product ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3465)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  (CheckAdvSIMDOrVFPEnabled true advsimd)
  if (advsimd : Bool)
  then
    (do
      let (addend, product) ← (( do
        let loop_r_lower : Nat := 0
        let loop_r_upper : Int := (regs -i 1)
        (do
          let mut loop_vars := (addend, product)
          for r in [loop_r_lower:loop_r_upper:1]i do
            let (addend, product) := loop_vars
            loop_vars ← do
              let loop_e_lower : Nat := 0
              let loop_e_upper : Int := (elements -i 1)
              (do
                let mut loop_vars_1 := (addend, product)
                for e in [loop_e_lower:loop_e_upper:1]i do
                  let (addend, product) := loop_vars_1
                  loop_vars_1 ← do
                    let w__0 ← (( do (D_read (n +i r)) ) : SailM (BitVec 64) )
                    let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 e esize)) ) :
                      SailM (BitVec esize) )
                    let w__2 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                    let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__2 e esize)) ) :
                      SailM (BitVec esize) )
                    let w__4 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                    let w__5 ← (( do (FPMul w__1 w__3 w__4) ) : SailM (BitVec esize) )
                    let product := (w__5 : (BitVec esize))
                    let w__7 ← (( do
                      if (add : Bool)
                      then (pure (product))
                      else
                        (do
                          (FPNeg product)) ) : SailM (BitVec esize) )
                    let addend := (w__7 : (BitVec esize))
                    let w__8 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                    let w__9 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                    let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__9 e esize)) ) :
                      SailM (BitVec esize) )
                    let w__11 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                    let w__12 ← (( do (FPAdd w__10 addend w__11) ) : SailM (BitVec esize) )
                    let w__13 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_set w__8 e esize
                        (Sail.BitVec.castWidth w__12))) ) : SailM (BitVec 64) )
                    (D_set (d +i r) w__13)
                    (pure ((addend, product)))
                (pure loop_vars_1))
          (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize)) )
      (pure (())))
  else
    (do
      match esize with
      | 16 =>
        (do
          let addend16 ← (( do
            if (add : Bool)
            then
              (do
                let w__14 ← (( do (S_read n) ) : SailM (BitVec 32) )
                let w__15 ← (( do (S_read m) ) : SailM (BitVec 32) )
                let w__16 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
                (FPMul (Sail.BitVec.extractLsb w__14 15 0) (Sail.BitVec.extractLsb w__15 15 0) w__16))
            else
              (do
                let w__18 ← (( do (S_read n) ) : SailM (BitVec 32) )
                let w__19 ← (( do (S_read m) ) : SailM (BitVec 32) )
                let w__20 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
                let w__21 ← (( do
                  (FPMul (Sail.BitVec.extractLsb w__18 15 0) (Sail.BitVec.extractLsb w__19 15 0)
                    w__20) ) : SailM (BitVec 16) )
                (FPNeg w__21)) ) : SailM (BitVec 16) )
          let w__23 ← (( do (S_read d) ) : SailM (BitVec 32) )
          let w__24 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__25 ← (( do (FPAdd (Sail.BitVec.extractLsb w__23 15 0) addend16 w__24) ) : SailM
            (BitVec 16) )
          (S_set d ((Zeros (n := 16)) +++ w__25)))
      | 32 =>
        (do
          let addend32 ← (( do
            if (add : Bool)
            then
              (do
                let w__26 ← (( do (S_read n) ) : SailM (BitVec 32) )
                let w__27 ← (( do (S_read m) ) : SailM (BitVec 32) )
                let w__28 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
                (FPMul w__26 w__27 w__28))
            else
              (do
                let w__30 ← (( do (S_read n) ) : SailM (BitVec 32) )
                let w__31 ← (( do (S_read m) ) : SailM (BitVec 32) )
                let w__32 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
                let w__33 ← (( do (FPMul w__30 w__31 w__32) ) : SailM (BitVec 32) )
                (FPNeg w__33)) ) : SailM (BitVec 32) )
          let w__35 ← (( do (S_read d) ) : SailM (BitVec 32) )
          let w__36 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__37 ← (( do (FPAdd w__35 addend32 w__36) ) : SailM (BitVec 32) )
          (S_set d w__37))
      | 64 =>
        (do
          let addend64 ← (( do
            if (add : Bool)
            then
              (do
                let w__38 ← (( do (D_read n) ) : SailM (BitVec 64) )
                let w__39 ← (( do (D_read m) ) : SailM (BitVec 64) )
                let w__40 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
                (FPMul w__38 w__39 w__40))
            else
              (do
                let w__42 ← (( do (D_read n) ) : SailM (BitVec 64) )
                let w__43 ← (( do (D_read m) ) : SailM (BitVec 64) )
                let w__44 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
                let w__45 ← (( do (FPMul w__42 w__43 w__44) ) : SailM (BitVec 64) )
                (FPNeg w__45)) ) : SailM (BitVec 64) )
          let w__47 ← (( do (D_read d) ) : SailM (BitVec 64) )
          let w__48 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__49 ← (( do (FPAdd w__47 addend64 w__48) ) : SailM (BitVec 64) )
          (D_set d w__49))
      | _ => (pure (())))


/-- Type quantifiers: k_add : Bool, d__arg : Nat, elements : Nat, esize : Nat, k_floating_point :
  Bool, index : Nat, k_is_unsigned : Bool, k_long_destination : Bool, m : Nat, n : Nat, regs : Nat, List.elem
  regs [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 15 ∧
  List.elem index [0, 1, 2, 3] ∧
  List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMLA_s_Op_A_txt (add : Bool) (d__arg : Nat) (elements : Nat) (esize : Nat) (floating_point : Bool) (index : Nat) (long_destination : Bool) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let addend ← (( do (undefined_int_at (← occLabel 3480) ()) ) : SailM Int )
  let fp_addend ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3481)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3482)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let op1val ← (( do (undefined_int_at (← occLabel 3483) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let w__0 ← (( do (Din_read m) ) : SailM (BitVec 64) )
  let op2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 index esize)) ) : SailM
    (BitVec esize) )
  let op2val ← (( do (asl_Int op2 is_unsigned) ) : SailM Int )
  let (addend, fp_addend, op1, op1val) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (addend, fp_addend, op1, op1val)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (addend, fp_addend, op1, op1val) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
          (do
            let mut loop_vars_1 := (addend, fp_addend, op1, op1val)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (addend, fp_addend, op1, op1val) := loop_vars_1
              loop_vars_1 ← do
                let w__1 ← (( do (Din_read (n +i r)) ) : SailM (BitVec 64) )
                let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e esize)) ) : SailM
                  (BitVec esize) )
                let op1 := (w__2 : (BitVec esize))
                let w__3 ← (( do (asl_Int op1 is_unsigned) ) : SailM Int )
                let op1val : Int := (w__3 : Int)
                let (addend, fp_addend) ← (( do
                  if (floating_point : Bool)
                  then
                    (do
                      let w__9 ← (( do
                        if (add : Bool)
                        then
                          (do
                            let w__4 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                            (FPMul op1 op2 w__4))
                        else
                          (do
                            let w__6 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                            let w__7 ← (( do (FPMul op1 op2 w__6) ) : SailM (BitVec esize) )
                            (FPNeg w__7)) ) : SailM (BitVec esize) )
                      let fp_addend := (w__9 : (BitVec esize))
                      let w__10 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                      let w__11 ← (( do (Din_read (d +i r)) ) : SailM (BitVec 64) )
                      let w__12 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__11 e esize)) )
                        : SailM (BitVec esize) )
                      let w__13 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                      let w__14 ← (( do (FPAdd w__12 fp_addend w__13) ) : SailM (BitVec esize) )
                      let w__15 ← (( do
                        ((Sail.BitVec.castWidth ) <$> (Elem_set w__10 e esize
                          (Sail.BitVec.castWidth w__14))) ) : SailM (BitVec 64) )
                      (D_set (d +i r) w__15)
                      (pure ((addend, fp_addend))))
                  else
                    (do
                      let addend : Int :=
                        if (add : Bool)
                        then (op1val *i op2val)
                        else ((Neg.neg op1val) *i op2val)
                      if (long_destination : Bool)
                      then
                        (do
                          let w__16 ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
                          let w__17 ← (( do (Qin_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
                          let w__18 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read w__17 e
                              (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM
                            (BitVec (2 * esize)) )
                          let w__19 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_set w__16 e
                              (Sail.Int.toNatChecked ((2 *i esize)))
                              (Sail.BitVec.castWidth (BitVec.addInt w__18 addend)))) ) : SailM
                            (BitVec 128) )
                          (Q_set (Int.shiftr d 1) w__19))
                      else
                        (do
                          let w__20 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                          let w__21 ← (( do (Din_read (d +i r)) ) : SailM (BitVec 64) )
                          let w__22 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_read w__21 e esize)) ) : SailM
                            (BitVec esize) )
                          let w__23 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (Elem_set w__20 e esize
                              (Sail.BitVec.castWidth (BitVec.addInt w__22 addend)))) ) : SailM
                            (BitVec 64) )
                          (D_set (d +i r) w__23))
                      (pure ((addend, fp_addend)))) ) : SailM (Int × (BitVec esize)) )
                (pure ((addend, fp_addend, op1, op1val)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Int × (BitVec esize) × (BitVec esize) × Int) )
  (pure (()))


/-- Type quantifiers: k_advsimd : Bool, d__arg : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, regs
  : Int, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMUL_f_Op_A_txt (advsimd : Bool) (d__arg : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (regs : Int) : SailM Unit := do
  let d : Int := d__arg
  (CheckAdvSIMDOrVFPEnabled true advsimd)
  if (advsimd : Bool)
  then
    (do
      let loop_r_lower : Nat := 0
      let loop_r_upper : Int := (regs -i 1)
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
                  let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e esize)) ) :
                    SailM (BitVec esize) )
                  let w__3 ← (( do (D_read (m +i r)) ) : SailM (BitVec 64) )
                  let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__3 e esize)) ) :
                    SailM (BitVec esize) )
                  let w__5 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                  let w__6 ← (( do (FPMul w__2 w__4 w__5) ) : SailM (BitVec esize) )
                  let w__7 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_set w__0 e esize
                      (Sail.BitVec.castWidth w__6))) ) : SailM (BitVec 64) )
                  (D_set (d +i r) w__7)
              (pure loop_vars_1))
        (pure loop_vars)))
  else
    (do
      match esize with
      | 16 =>
        (do
          let w__8 ← (( do (S_read n) ) : SailM (BitVec 32) )
          let w__9 ← (( do (S_read m) ) : SailM (BitVec 32) )
          let w__10 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__11 ← (( do
            (FPMul (Sail.BitVec.extractLsb w__8 15 0) (Sail.BitVec.extractLsb w__9 15 0) w__10) ) :
            SailM (BitVec 16) )
          (S_set d ((Zeros (n := 16)) +++ w__11)))
      | 32 =>
        (do
          let w__12 ← (( do (S_read n) ) : SailM (BitVec 32) )
          let w__13 ← (( do (S_read m) ) : SailM (BitVec 32) )
          let w__14 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__15 ← (( do (FPMul w__12 w__13 w__14) ) : SailM (BitVec 32) )
          (S_set d w__15))
      | 64 =>
        (do
          let w__16 ← (( do (D_read n) ) : SailM (BitVec 64) )
          let w__17 ← (( do (D_read m) ) : SailM (BitVec 64) )
          let w__18 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
          let w__19 ← (( do (FPMul w__16 w__17 w__18) ) : SailM (BitVec 64) )
          (D_set d w__19))
      | _ => (pure (())))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_floating_point : Bool, index :
  Nat, k_is_unsigned : Bool, k_long_destination : Bool, m : Nat, n : Nat, regs : Nat, List.elem regs
  [1, 2] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 15 ∧
  List.elem index [0, 1, 2, 3] ∧
  List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VMUL_s_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (floating_point : Bool) (index : Nat) (long_destination : Bool) (m : Nat) (n : Nat) (regs : Nat) (is_unsigned : Bool) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3538)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let op1val ← (( do (undefined_int_at (← occLabel 3539) ()) ) : SailM Int )
  (CheckAdvSIMDEnabled ())
  let w__0 ← (( do (Din_read m) ) : SailM (BitVec 64) )
  let op2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__0 index esize)) ) : SailM
    (BitVec esize) )
  let op2val ← (( do (asl_Int op2 is_unsigned) ) : SailM Int )
  let (op1, op1val) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((regs -i 1)))
    (do
      let mut loop_vars := (op1, op1val)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (op1, op1val) := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
          (do
            let mut loop_vars_1 := (op1, op1val)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (op1, op1val) := loop_vars_1
              loop_vars_1 ← do
                let w__1 ← (( do (Din_read (n +i r)) ) : SailM (BitVec 64) )
                let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read w__1 e esize)) ) : SailM
                  (BitVec esize) )
                let op1 := (w__2 : (BitVec esize))
                let w__3 ← (( do (asl_Int op1 is_unsigned) ) : SailM Int )
                let op1val : Int := (w__3 : Int)
                if (floating_point : Bool)
                then
                  (do
                    let w__4 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                    let w__5 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                    let w__6 ← (( do (FPMul op1 op2 w__5) ) : SailM (BitVec esize) )
                    let w__7 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_set w__4 e esize
                        (Sail.BitVec.castWidth w__6))) ) : SailM (BitVec 64) )
                    (D_set (d +i r) w__7))
                else
                  (do
                    if (long_destination : Bool)
                    then
                      (do
                        let w__8 ← (( do (Q_read (Int.shiftr d 1)) ) : SailM (BitVec 128) )
                        let w__9 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_set w__8 e
                            (Sail.Int.toNatChecked ((2 *i esize)))
                            (Sail.BitVec.castWidth (integer_subrange (op1val *i op2val)
                              ((2 *i esize) -i 1) 0)))) ) : SailM (BitVec 128) )
                        (Q_set (Int.shiftr d 1) w__9))
                    else
                      (do
                        let w__10 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                        let w__11 ← (( do
                          ((Sail.BitVec.castWidth ) <$> (Elem_set w__10 e esize
                            (Sail.BitVec.castWidth (integer_subrange (op1val *i op2val) (esize -i 1)
                              0)))) ) : SailM (BitVec 64) )
                        (D_set (d +i r) w__11)))
                (pure ((op1, op1val)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM ((BitVec esize) × Int) )
  (pure (()))


def decode_aarch32_instrs_VNEG_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__4 ← (( do
        if (((F == 1#1) : Bool) : Bool)
        then
          (do
            (pure ((← do
                  if (((size == 0b01#2) : Bool) : Bool)
                  then
                    (do
                      let w__1 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
                      (pure (((! w__1) : Bool))))
                  else (pure false)) || ((size == 0b00#2) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let advsimd : Bool := true
      let floating_point : Bool := (F == 1#1)
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VNEG_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) floating_point (Sail.Int.toNatChecked (m)) regs))
  else (pure (()))


def decode_aarch32_instrs_VNEG_A2enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:30572.29-30572.30"
      let floating_point ← (( do (undefined_bool_at (← occLabel 3549) ()) ) : SailM Bool )
      let elements ← (( do (undefined_int_at (← occLabel 3550) ()) ) : SailM Int )
      let regs ← (( do (undefined_int_at (← occLabel 3551) ()) ) : SailM Int )
      let w__3 ← (( do
        if (((size == 0b00#2) : Bool) : Bool)
        then (pure true)
        else
          (do
            if (((size == 0b01#2) : Bool) : Bool)
            then
              (do
                let w__1 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
                (pure (((! w__1) : Bool))))
            else (pure false)) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__6 ← (( do
        if ((← do
             let w__4 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
             (pure ((((_get_FPSCR_Type_length w__4) != 0b000#3) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__5 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
            (pure ((((_get_FPSCR_Type_Stride w__5) != 0b00#2) : Bool)))) ) : SailM Bool )
      if (w__6 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let regs : Int := regs
      let elements : Int := elements
      let floating_point := floating_point
      let advsimd : Bool := false
      let esize : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3552) 0 31))) ) :
        SailM Nat )
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3553) 0 31))) ) :
        SailM Nat )
      let (d, esize, m) : (Nat × Int × Nat) :=
        match size with
        | 0b01 =>
          (let esize : Int := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m))
        | 0b10 =>
          (let esize : Int := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m))
        | 0b11 =>
          (let esize : Int := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          (d, esize, m))
        | _ => (d, esize, m)
      let m : Int := m
      let esize : Int := esize
      let d : Int := d
      (execute_aarch32_instrs_VNEG_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) floating_point (Sail.Int.toNatChecked (m)) regs))
  else (pure (()))


def decode_aarch32_instrs_VNEG_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__4 ← (( do
        if (((F == 1#1) : Bool) : Bool)
        then
          (do
            (pure ((← do
                  if (((size == 0b01#2) : Bool) : Bool)
                  then
                    (do
                      let w__1 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
                      (pure (((! w__1) : Bool))))
                  else (pure false)) || ((size == 0b00#2) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__6 ← (( do
        if ((((F == 1#1) && (size == 0b01#2)) : Bool) : Bool)
        then
          (do
            (InITBlock ()))
        else (pure false) ) : SailM Bool )
      if (w__6 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   Vm 0)])) == 1#1))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let advsimd : Bool := true
      let floating_point : Bool := (F == 1#1)
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 (Sail.Int.toNatChecked (esize)))
      let d : Int := (BitVec.toNat (D +++ Vd))
      let m : Int := (BitVec.toNat (M +++ Vm))
      let regs : Int :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VNEG_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) floating_point (Sail.Int.toNatChecked (m)) regs))
  else (pure (()))


def decode_aarch32_instrs_VNEG_T2enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let floating_point ← (( do (undefined_bool_at (← occLabel 3554) ()) ) : SailM Bool )
      let elements ← (( do (undefined_int_at (← occLabel 3555) ()) ) : SailM Int )
      let regs ← (( do (undefined_int_at (← occLabel 3556) ()) ) : SailM Int )
      let w__3 ← (( do
        if (((size == 0b00#2) : Bool) : Bool)
        then (pure true)
        else
          (do
            if (((size == 0b01#2) : Bool) : Bool)
            then
              (do
                let w__1 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
                (pure (((! w__1) : Bool))))
            else (pure false)) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__5 ← (( do
        if (((size == 0b01#2) : Bool) : Bool)
        then
          (do
            (InITBlock ()))
        else (pure false) ) : SailM Bool )
      if (w__5 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__8 ← (( do
        if ((← do
             let w__6 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
             (pure ((((_get_FPSCR_Type_length w__6) != 0b000#3) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__7 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
            (pure ((((_get_FPSCR_Type_Stride w__7) != 0b00#2) : Bool)))) ) : SailM Bool )
      if (w__8 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let regs : Int := regs
      let elements : Int := elements
      let floating_point := floating_point
      let advsimd : Bool := false
      let esize : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3557) 0 31))) ) :
        SailM Nat )
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3558) 0 31))) ) :
        SailM Nat )
      let (d, esize, m) : (Nat × Int × Nat) :=
        match size with
        | 0b01 =>
          (let esize : Int := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m))
        | 0b10 =>
          (let esize : Int := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m))
        | 0b11 =>
          (let esize : Int := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          (d, esize, m))
        | _ => (d, esize, m)
      let m : Int := m
      let esize : Int := esize
      let d : Int := d
      (execute_aarch32_instrs_VNEG_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) floating_point (Sail.Int.toNatChecked (m)) regs))
  else (pure (()))


end ArmFull.Functions
