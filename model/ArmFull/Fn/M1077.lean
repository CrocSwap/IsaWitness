import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0023
import ArmFull.Fn.M0043
import ArmFull.Fn.M0049
import ArmFull.Fn.M0061
import ArmFull.Fn.M0087
import ArmFull.Fn.M0099
import ArmFull.Fn.M0116
import ArmFull.Fn.M0118
import ArmFull.Fn.M0124
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0149
import ArmFull.Fn.M0150
import ArmFull.Fn.M0178
import ArmFull.Fn.M0203
import ArmFull.Fn.M0215
import ArmFull.Fn.M0216
import ArmFull.Fn.M0228
import ArmFull.Fn.M0237
import ArmFull.Fn.M0257
import ArmFull.Fn.M0840
import ArmFull.Fn.M0852
import ArmFull.Fn.M0925
import ArmFull.Fn.M1040
import ArmFull.Fn.M1041
import ArmFull.Fn.M1042
import ArmFull.Fn.M1043

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

/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_exact : Bool, m : Nat, regs : Nat, List.elem
  regs [1, 2] ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRINTX_asimd_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (exact : Bool) (m : Nat) (regs : Nat) (rounding : FPRounding) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3825)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3826)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
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
                let w__2 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                let w__3 ← (( do (FPRoundInt op1 w__2 rounding exact) ) : SailM (BitVec esize) )
                let result := (w__3 : (BitVec esize))
                let w__4 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__5 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__4 e esize
                    (Sail.BitVec.castWidth result))) ) : SailM (BitVec 64) )
                (D_set (d +i r) w__5)
                (pure ((op1, result)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize)) )
  (pure (()))


/-- Type quantifiers: d : Nat, esize : Nat, k_exact : Bool, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VRINTX_vfp_Op_A_txt (d : Nat) (esize : Nat) (exact : Bool) (m : Nat) : SailM Unit := do
  (CheckVFPEnabled true)
  let w__0 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
  let rounding ← (( do (FPRoundingMode w__0) ) : SailM FPRounding )
  match esize with
  | 16 =>
    (do
      let w__1 ← (( do (S_read m) ) : SailM (BitVec 32) )
      let w__2 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let w__3 ← (( do (FPRoundInt (Sail.BitVec.extractLsb w__1 15 0) w__2 rounding exact) ) :
        SailM (BitVec 16) )
      (S_set d ((Zeros (n := 16)) +++ w__3)))
  | 32 =>
    (do
      let w__4 ← (( do (S_read m) ) : SailM (BitVec 32) )
      let w__5 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let w__6 ← (( do (FPRoundInt w__4 w__5 rounding exact) ) : SailM (BitVec 32) )
      (S_set d w__6))
  | 64 =>
    (do
      let w__7 ← (( do (D_read m) ) : SailM (BitVec 64) )
      let w__8 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let w__9 ← (( do (FPRoundInt w__7 w__8 rounding exact) ) : SailM (BitVec 64) )
      (D_set d w__9))
  | _ => (pure (()))


/-- Type quantifiers: d__arg : Nat, elements : Nat, esize : Nat, k_exact : Bool, m : Nat, regs : Nat, List.elem
  regs [1, 2] ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [16, 32] ∧ List.elem elements [2, 4] ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 -/
def execute_aarch32_instrs_VRINTZ_asimd_Op_A_txt (d__arg : Nat) (elements : Nat) (esize : Nat) (exact : Bool) (m : Nat) (regs : Nat) (rounding : FPRounding) : SailM Unit := do
  let d : Int := d__arg
  let op1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3831)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3832)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  (CheckAdvSIMDEnabled ())
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
                let w__2 ← (( do (StandardFPSCRValue ()) ) : SailM (BitVec 64) )
                let w__3 ← (( do (FPRoundInt op1 w__2 rounding exact) ) : SailM (BitVec esize) )
                let result := (w__3 : (BitVec esize))
                let w__4 ← (( do (D_read (d +i r)) ) : SailM (BitVec 64) )
                let w__5 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_set w__4 e esize
                    (Sail.BitVec.castWidth result))) ) : SailM (BitVec 64) )
                (D_set (d +i r) w__5)
                (pure ((op1, result)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize)) )
  (pure (()))


/-- Type quantifiers: d : Nat, esize : Nat, k_exact : Bool, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VRINTZ_vfp_Op_A_txt (d : Nat) (esize : Nat) (exact : Bool) (m : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckVFPEnabled true)
  match esize with
  | 16 =>
    (do
      let w__0 ← (( do (S_read m) ) : SailM (BitVec 32) )
      let w__1 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let w__2 ← (( do (FPRoundInt (Sail.BitVec.extractLsb w__0 15 0) w__1 rounding exact) ) :
        SailM (BitVec 16) )
      (S_set d ((Zeros (n := 16)) +++ w__2)))
  | 32 =>
    (do
      let w__3 ← (( do (S_read m) ) : SailM (BitVec 32) )
      let w__4 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let w__5 ← (( do (FPRoundInt w__3 w__4 rounding exact) ) : SailM (BitVec 32) )
      (S_set d w__5))
  | 64 =>
    (do
      let w__6 ← (( do (D_read m) ) : SailM (BitVec 64) )
      let w__7 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
      let w__8 ← (( do (FPRoundInt w__6 w__7 rounding exact) ) : SailM (BitVec 64) )
      (D_set d w__8))
  | _ => (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_VJCVT_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  (CheckVFPEnabled true)
  let fltval ← (( do (D_read m) ) : SailM (BitVec 64) )
  let intval ← (( do (undefined_bitvector_at (← occLabel 3852) 32) ) : SailM (BitVec 32) )
  let Z ← (( do (undefined_bitvector_at (← occLabel 3853) 1) ) : SailM (BitVec 1) )
  let w__0 ← (( do (FPSCR_read ()) ) : SailM (BitVec 64) )
  let w__1 ← (( do (FPToFixedJS (k_M := 64) fltval w__0 false 32) ) : SailM
    ((BitVec 32) × (BitVec 1)) )
  let (tup__0, tup__1) := (w__1 : ((BitVec 32) × (BitVec 1)))
  let intval : (BitVec 32) := tup__0
  let Z : (BitVec 1) := tup__1
  let w__2 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
  (FPSCR_write (Mk_FPSCR_Type (Sail.BitVec.updateSubrange w__2 31 28 ((0#1 +++ Z) +++ 0b00#2))))
  (S_set d intval)


/-- Type quantifiers: k_acquire : Bool, datasize : Nat, n : Nat, regsize : Nat, k_release : Bool, s
  : Nat, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ s ∧
  s ≤ 31 ∧
  List.elem regsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_atomicops_cas_single (acquire : Bool) (datasize : Nat) (n : Nat) (regsize : Nat) (release : Bool) (s : Nat) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4027) 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescAtomicOp MemAtomicOp_CAS acquire release tagchecked) ) : SailM
    AccessDescriptor )
  let comparevalue ← (( do ((Sail.BitVec.castWidth ) <$> (X_read s datasize)) ) : SailM
    (BitVec datasize) )
  let newvalue ← (( do ((Sail.BitVec.castWidth ) <$> (X_read t datasize)) ) : SailM
    (BitVec datasize) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let data ← (( do (MemAtomic address comparevalue newvalue accdesc) ) : SailM (BitVec datasize) )
  ArmFull.assert (regsize ≥b datasize) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:6398.44-6398.45"
  (X_set s regsize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend data regsize)))
  let w__2 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let ar : (BitVec 1) :=
        if ((acquire || release) : Bool)
        then 1#1
        else 0#1
      let excl : (BitVec 1) := 0#1
      let at' : (BitVec 1) := 1#1
      let is_load : Bool := true
      (SPESampleExtendedLoadStore ar excl at' is_load))
  else (pure (()))


/-- Type quantifiers: k_acquire : Bool, datasize : Nat, n : Nat, k_release : Bool, s : Nat, t : Nat, k_tagchecked
  : Bool, 0 ≤ t ∧
  t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64] -/
def execute_aarch64_instrs_memory_atomicops_cas_pair (acquire : Bool) (datasize : Nat) (n : Nat) (release : Bool) (s : Nat) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4028) 64) ) : SailM (BitVec 64) )
  let s1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read s datasize)) ) : SailM (BitVec datasize) )
  let s2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read (s +i 1) datasize)) ) : SailM
    (BitVec datasize) )
  let t1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read t datasize)) ) : SailM (BitVec datasize) )
  let t2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read (t +i 1) datasize)) ) : SailM
    (BitVec datasize) )
  let accdesc ← (( do (CreateAccDescAtomicOp MemAtomicOp_CAS acquire release tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  let comparevalue : (BitVec (2 * datasize)) :=
    if (w__0 : Bool)
    then (Sail.BitVec.castWidth (s1 +++ s2))
    else (Sail.BitVec.castWidth (s2 +++ s1))
  let w__1 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  let newvalue : (BitVec (2 * datasize)) :=
    if (w__1 : Bool)
    then (Sail.BitVec.castWidth (t1 +++ t2))
    else (Sail.BitVec.castWidth (t2 +++ t1))
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let data ← (( do (MemAtomic address comparevalue newvalue accdesc) ) : SailM
    (BitVec (2 * datasize)) )
  let w__4 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      (X_set s datasize
        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb data
          (Sail.Int.toNatChecked (((2 *i datasize) -i 1))) datasize)))
      (X_set (s +i 1) datasize
        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb data
          (Sail.Int.toNatChecked ((datasize -i 1))) 0))))
  else
    (do
      (X_set s datasize
        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb data
          (Sail.Int.toNatChecked ((datasize -i 1))) 0)))
      (X_set (s +i 1) datasize
        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb data
          (Sail.Int.toNatChecked (((2 *i datasize) -i 1))) datasize))))
  let w__5 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      let ar : (BitVec 1) :=
        if ((acquire || release) : Bool)
        then 1#1
        else 0#1
      let excl : (BitVec 1) := 0#1
      let at' : (BitVec 1) := 1#1
      let is_load : Bool := true
      (SPESampleExtendedLoadStore ar excl at' is_load))
  else (pure (()))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, k_neg : Bool, 0
  ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (neg : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4111)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4112)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let element := (w__0 : (BitVec esize))
          let element ← (( do
            if (neg : Bool)
            then
              (do
                (FPNeg element))
            else
              (do
                (FPAbs element)) ) : SailM (BitVec esize) )
          let w__3 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth element)) ) : SailM
            (BitVec datasize) )
          let result := (w__3 : (BitVec datasize))
          (pure ((element, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: k_abs : Bool, d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n
  : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd (abs : Bool) (cmp : CompareOp) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let element1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4113)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let element2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4114)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let test_passed ← (( do (undefined_bool_at (← occLabel 4115) ()) ) : SailM Bool )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do
    if (((elements == 1) : Bool) : Bool)
    then
      (do
        (IsMerging fpcr))
    else (pure false) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then
      (do
        (V_read m 128))
    else (pure ((Zeros (n := 128)))) ) : SailM (BitVec 128) )
  let (element1, element2, result, test_passed) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element1, element2, result, test_passed)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element1, element2, result, test_passed) := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 := (w__2 : (BitVec esize))
          let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 := (w__3 : (BitVec esize))
          let (element1, element2) ← (( do
            if (abs : Bool)
            then
              (do
                let w__4 ← (( do (FPAbs element1) ) : SailM (BitVec esize) )
                let element1 := (w__4 : (BitVec esize))
                let w__5 ← (( do (FPAbs element2) ) : SailM (BitVec esize) )
                let element2 := (w__5 : (BitVec esize))
                (pure ((element1, element2))))
            else (pure ((element1, element2))) ) : SailM ((BitVec esize) × (BitVec esize)) )
          let test_passed ← (( do
            match cmp with
            | .CompareOp_EQ =>
              (do
                (FPCompareEQ element1 element2 fpcr))
            | .CompareOp_GE =>
              (do
                (FPCompareGE element1 element2 fpcr))
            | .CompareOp_GT =>
              (do
                (FPCompareGT element1 element2 fpcr))
            | _ => (pure (test_passed)) ) : SailM Bool )
          let w__9 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
              (Sail.BitVec.castWidth (if (test_passed : Bool)
              then (Ones (n := esize))
              else (Zeros (n := esize)))))) ) : SailM (BitVec 128) )
          let result := (w__9 : (BitVec 128))
          (pure ((element1, element2, result, test_passed)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec 128) × Bool) )
  (V_set d 128 result)


/-- Type quantifiers: datasize : Nat, m : Nat, n : Nat, k_signal_all_nans : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [16, 32, 64] -/
def execute_aarch64_instrs_float_compare_cond (condition : (BitVec 4)) (datasize : Nat) (flags__arg : (BitVec 4)) (m : Nat) (n : Nat) (signal_all_nans : Bool) : SailM Unit := do
  let flags : (BitVec 4) := flags__arg
  (CheckFPEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let taken : Bool := false
  let w__0 ← (( do (ConditionHolds condition) ) : SailM Bool )
  let (flags, taken) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
        let w__2 ← (( do (FPCompare operand1 operand2 signal_all_nans w__1) ) : SailM (BitVec 4) )
        let flags := (w__2 : (BitVec 4))
        let taken : Bool := true
        (pure ((flags, taken))))
    else (pure ((flags, taken))) ) : SailM ((BitVec 4) × Bool) )
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__3 with N := (Sail.BitVec.extractLsb flags 3 3) }
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__4 with Z := (Sail.BitVec.extractLsb flags 2 2) }
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with C := (Sail.BitVec.extractLsb flags 1 1) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with V := (Sail.BitVec.extractLsb flags 0 0) }
  let w__7 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__7 : Bool)
  then
    (do
      let conditional : Bool := true
      (SPESampleAddOpOther conditional taken))
  else (pure (()))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd (comparison : CompareOp) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4162)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let zero ← (( do ((Sail.BitVec.castWidth ) <$> (FPZero 0#1 esize)) ) : SailM (BitVec esize) )
  let element ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4163)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let test_passed ← (( do (undefined_bool_at (← occLabel 4164) ()) ) : SailM Bool )
  let (element, result, test_passed) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result, test_passed)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result, test_passed) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let element := (w__0 : (BitVec esize))
          let test_passed ← (( do
            match comparison with
            | .CompareOp_GT =>
              (do
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                (FPCompareGT element zero w__1))
            | .CompareOp_GE =>
              (do
                let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                (FPCompareGE element zero w__3))
            | .CompareOp_EQ =>
              (do
                let w__5 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                (FPCompareEQ element zero w__5))
            | .CompareOp_LE =>
              (do
                let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                (FPCompareGE zero element w__7))
            | .CompareOp_LT =>
              (do
                let w__9 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                (FPCompareGT zero element w__9)) ) : SailM Bool )
          let w__11 ← (( do
            (Elem_set result e esize
              (Sail.BitVec.castWidth (if (test_passed : Bool)
              then (Ones (n := esize))
              else (Zeros (n := esize))))) ) : SailM (BitVec datasize) )
          let result := (w__11 : (BitVec datasize))
          (pure ((element, result, test_passed)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec datasize) × Bool) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd (comparison : CompareOp) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4192)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let zero ← (( do ((Sail.BitVec.castWidth ) <$> (FPZero 0#1 esize)) ) : SailM (BitVec esize) )
  let element ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4193)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let test_passed ← (( do (undefined_bool_at (← occLabel 4194) ()) ) : SailM Bool )
  let (element, result, test_passed) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result, test_passed)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result, test_passed) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let element := (w__0 : (BitVec esize))
          let test_passed ← (( do
            match comparison with
            | .CompareOp_GT =>
              (do
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                (FPCompareGT element zero w__1))
            | .CompareOp_GE =>
              (do
                let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                (FPCompareGE element zero w__3))
            | .CompareOp_EQ =>
              (do
                let w__5 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                (FPCompareEQ element zero w__5))
            | .CompareOp_LE =>
              (do
                let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                (FPCompareGE zero element w__7))
            | .CompareOp_LT =>
              (do
                let w__9 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                (FPCompareGT zero element w__9)) ) : SailM Bool )
          let w__11 ← (( do
            (Elem_set result e esize
              (Sail.BitVec.castWidth (if (test_passed : Bool)
              then (Ones (n := esize))
              else (Zeros (n := esize))))) ) : SailM (BitVec datasize) )
          let result := (w__11 : (BitVec datasize))
          (pure ((element, result, test_passed)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec datasize) × Bool) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: k_cmp_with_zero : Bool, datasize : Nat, m : Nat, n : Nat, k_signal_all_nans :
  Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [16, 32, 64] -/
def execute_aarch64_instrs_float_compare_uncond (cmp_with_zero : Bool) (datasize : Nat) (m : Nat) (n : Nat) (signal_all_nans : Bool) : SailM Unit := do
  (CheckFPEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do
    if (cmp_with_zero : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (FPZero 0#1 datasize)))
    else
      (do
        ((Sail.BitVec.castWidth ) <$> (V_read m datasize))) ) : SailM (BitVec datasize) )
  let w__2 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
  let split_vec ← (( do (FPCompare operand1 operand2 signal_all_nans w__2) ) : SailM (BitVec 4) )
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__3 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__4 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with V := (Sail.BitVec.extractLsb split_vec 0 0) }


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, n
  : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let element ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4195)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do
    if (((elements == 1) : Bool) : Bool)
    then
      (do
        (IsMerging fpcr))
    else (pure false) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then
      (do
        (V_read d 128))
    else (pure ((Zeros (n := 128)))) ) : SailM (BitVec 128) )
  let (element, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result) := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let element := (w__2 : (BitVec esize))
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (FPToFixed element 0 is_unsigned fpcr rounding esize)) ) :
            SailM (BitVec esize) )
          let w__4 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__3))) )
            : SailM (BitVec 128) )
          let result := (w__4 : (BitVec 128))
          (pure ((element, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)


end ArmFull.Functions
