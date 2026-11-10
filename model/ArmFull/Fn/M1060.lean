import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0017
import ArmFull.Fn.M0045
import ArmFull.Fn.M0086
import ArmFull.Fn.M0114
import ArmFull.Fn.M0124
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0175
import ArmFull.Fn.M0228
import ArmFull.Fn.M1003
import ArmFull.Fn.M1013
import ArmFull.Fn.M1014
import ArmFull.Fn.M1017

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

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_SHA1P_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let t ← (( do (undefined_bitvector_at (← occLabel 3799) 32) ) : SailM (BitVec 32) )
  (CheckCryptoEnabled32 ())
  let x ← (( do (Q_read (Int.shiftl d 1)) ) : SailM (BitVec 128) )
  let w__0 ← (( do (Q_read (Int.shiftl n 1)) ) : SailM (BitVec 128) )
  let y : (BitVec 32) := (Sail.BitVec.extractLsb w__0 31 0)
  let w ← (( do (Q_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
  let (t, x, y) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := 3
    (do
      let mut loop_vars := (t, x, y)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (t, x, y) := loop_vars
        loop_vars ← do
          let t : (BitVec 32) :=
            (SHAparity (Sail.BitVec.extractLsb x 63 32) (Sail.BitVec.extractLsb x 95 64)
              (Sail.BitVec.extractLsb x 127 96))
          let w__1 ← (( do (ROL (Sail.BitVec.extractLsb x 31 0) 5) ) : SailM (BitVec 32) )
          let w__2 ← (( do (Elem_read w e 32) ) : SailM (BitVec 32) )
          let y := ((((y + w__1) + t) + w__2) : (BitVec 32))
          let w__3 ← (( do (ROL (Sail.BitVec.extractLsb x 63 32) 30) ) : SailM (BitVec 32) )
          let x := ((Sail.BitVec.updateSubrange x 63 32 w__3) : (BitVec 128))
          let split_vec ← (( do (ROL (y +++ x) 32) ) : SailM (BitVec (32 + 128)) )
          let y : (BitVec 32) := (Sail.BitVec.extractLsb split_vec 159 128)
          let x : (BitVec 128) := (Sail.BitVec.extractLsb split_vec 127 0)
          (pure ((t, x, y)))
      (pure loop_vars)) ) : SailM ((BitVec 32) × (BitVec 128) × (BitVec 32)) )
  (Q_set (Int.shiftl d 1) x)


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_SHA1SU0_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckCryptoEnabled32 ())
  let op1 ← (( do (Q_read (Int.shiftl d 1)) ) : SailM (BitVec 128) )
  let op2 ← (( do (Q_read (Int.shiftl n 1)) ) : SailM (BitVec 128) )
  let op3 ← (( do (Q_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
  let op2 : (BitVec 128) :=
    ((Sail.BitVec.extractLsb op2 63 0) +++ (Sail.BitVec.extractLsb op1 127 64))
  (Q_set (Int.shiftl d 1) ((op1 ^^^ op2) ^^^ op3))


/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_SHA1SU1_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  (CheckCryptoEnabled32 ())
  let X ← (( do (Q_read (Int.shiftl d 1)) ) : SailM (BitVec 128) )
  let Y ← (( do (Q_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
  let T : (BitVec 128) := (X ^^^ (Y >>> 32))
  let W0 ← (( do (ROL (Sail.BitVec.extractLsb T 31 0) 1) ) : SailM (BitVec 32) )
  let W1 ← (( do (ROL (Sail.BitVec.extractLsb T 63 32) 1) ) : SailM (BitVec 32) )
  let W2 ← (( do (ROL (Sail.BitVec.extractLsb T 95 64) 1) ) : SailM (BitVec 32) )
  let w__0 ← (( do (ROL (Sail.BitVec.extractLsb T 127 96) 1) ) : SailM (BitVec 32) )
  let w__1 ← (( do (ROL (Sail.BitVec.extractLsb T 31 0) 2) ) : SailM (BitVec 32) )
  let W3 : (BitVec 32) := (w__0 ^^^ w__1)
  (Q_set (Int.shiftl d 1) (((W3 +++ W2) +++ W1) +++ W0))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_SHA256H_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckCryptoEnabled32 ())
  let X ← (( do (Q_read (Int.shiftl d 1)) ) : SailM (BitVec 128) )
  let Y ← (( do (Q_read (Int.shiftl n 1)) ) : SailM (BitVec 128) )
  let W ← (( do (Q_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
  let part1 : Bool := true
  let w__0 ← (( do (SHA256hash X Y W part1) ) : SailM (BitVec 128) )
  (Q_set (Int.shiftl d 1) w__0)


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_SHA256H2_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckCryptoEnabled32 ())
  let X ← (( do (Q_read (Int.shiftl n 1)) ) : SailM (BitVec 128) )
  let Y ← (( do (Q_read (Int.shiftl d 1)) ) : SailM (BitVec 128) )
  let W ← (( do (Q_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
  let part1 : Bool := false
  let w__0 ← (( do (SHA256hash X Y W part1) ) : SailM (BitVec 128) )
  (Q_set (Int.shiftl d 1) w__0)


/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_SHA256SU0_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  let elt ← (( do (undefined_bitvector_at (← occLabel 3800) 32) ) : SailM (BitVec 32) )
  (CheckCryptoEnabled32 ())
  let result ← (( do (undefined_bitvector_at (← occLabel 3801) 128) ) : SailM (BitVec 128) )
  let x ← (( do (Q_read (Int.shiftl d 1)) ) : SailM (BitVec 128) )
  let y ← (( do (Q_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
  let t : (BitVec 128) := ((Sail.BitVec.extractLsb y 31 0) +++ (Sail.BitVec.extractLsb x 127 32))
  let (elt, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := 3
    (do
      let mut loop_vars := (elt, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (elt, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Elem_read t e 32) ) : SailM (BitVec 32) )
          let elt := (w__0 : (BitVec 32))
          let elt : (BitVec 32) := (((ROR elt 7) ^^^ (ROR elt 18)) ^^^ (elt >>> 3))
          let w__1 ← (( do (Elem_read x e 32) ) : SailM (BitVec 32) )
          let w__2 ← (( do (Elem_set result e 32 (elt + w__1)) ) : SailM (BitVec 128) )
          let result := (w__2 : (BitVec 128))
          (pure ((elt, result)))
      (pure loop_vars)) ) : SailM ((BitVec 32) × (BitVec 128)) )
  (Q_set (Int.shiftl d 1) result)


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch32_instrs_SHA256SU1_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckCryptoEnabled32 ())
  let elt ← (( do (undefined_bitvector_at (← occLabel 3802) 32) ) : SailM (BitVec 32) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3803) 128) ) : SailM (BitVec 128) )
  let x ← (( do (Q_read (Int.shiftl d 1)) ) : SailM (BitVec 128) )
  let y ← (( do (Q_read (Int.shiftl n 1)) ) : SailM (BitVec 128) )
  let z ← (( do (Q_read (Int.shiftl m 1)) ) : SailM (BitVec 128) )
  let T0 : (BitVec 128) := ((Sail.BitVec.extractLsb z 31 0) +++ (Sail.BitVec.extractLsb y 127 32))
  let T1 : (BitVec 64) := (Sail.BitVec.extractLsb z 127 64)
  let (elt, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := 1
    (do
      let mut loop_vars := (elt, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (elt, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Elem_read T1 e 32) ) : SailM (BitVec 32) )
          let elt := (w__0 : (BitVec 32))
          let elt : (BitVec 32) := (((ROR elt 17) ^^^ (ROR elt 19)) ^^^ (elt >>> 10))
          let w__1 ← (( do (Elem_read x e 32) ) : SailM (BitVec 32) )
          let w__2 ← (( do (Elem_read T0 e 32) ) : SailM (BitVec 32) )
          let elt := (((elt + w__1) + w__2) : (BitVec 32))
          let w__3 ← (( do (Elem_set result e 32 elt) ) : SailM (BitVec 128) )
          let result := (w__3 : (BitVec 128))
          (pure ((elt, result)))
      (pure loop_vars)) ) : SailM ((BitVec 32) × (BitVec 128)) )
  let T1 : (BitVec 64) := (Sail.BitVec.extractLsb result 63 0)
  let (elt, result) ← (( do
    let loop_e_lower : Nat := 2
    let loop_e_upper : Nat := 3
    (do
      let mut loop_vars := (elt, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (elt, result) := loop_vars
        loop_vars ← do
          let w__4 ← (( do (Elem_read T1 (e -i 2) 32) ) : SailM (BitVec 32) )
          let elt := (w__4 : (BitVec 32))
          let elt : (BitVec 32) := (((ROR elt 17) ^^^ (ROR elt 19)) ^^^ (elt >>> 10))
          let w__5 ← (( do (Elem_read x e 32) ) : SailM (BitVec 32) )
          let w__6 ← (( do (Elem_read T0 e 32) ) : SailM (BitVec 32) )
          let elt := (((elt + w__5) + w__6) : (BitVec 32))
          let w__7 ← (( do (Elem_set result e 32 elt) ) : SailM (BitVec 128) )
          let result := (w__7 : (BitVec 128))
          (pure ((elt, result)))
      (pure loop_vars)) ) : SailM ((BitVec 32) × (BitVec 128)) )
  (Q_set (Int.shiftl d 1) result)


def decode_aarch32_instrs_VSEL_A1enc_A_txt (D : (BitVec 1)) (cc : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := 16
  let d ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3837) 0 31))) ) :
    SailM Nat )
  let n ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3838) 0 31))) ) :
    SailM Nat )
  let m ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3839) 0 31))) ) :
    SailM Nat )
  let (d, esize, m, n) : (Nat × Int × Nat × Nat) :=
    match size with
    | 0b01 =>
      (let esize : Int := 16
      let d : Nat := (BitVec.toNat (Vd +++ D))
      let n : Nat := (BitVec.toNat (Vn +++ N))
      let m : Nat := (BitVec.toNat (Vm +++ M))
      (d, esize, m, n))
    | 0b10 =>
      (let esize : Int := 32
      let d : Nat := (BitVec.toNat (Vd +++ D))
      let n : Nat := (BitVec.toNat (Vn +++ N))
      let m : Nat := (BitVec.toNat (Vm +++ M))
      (d, esize, m, n))
    | 0b11 =>
      (let esize : Int := 64
      let d : Nat := (BitVec.toNat (D +++ Vd))
      let n : Nat := (BitVec.toNat (N +++ Vn))
      let m : Nat := (BitVec.toNat (M +++ Vm))
      (d, esize, m, n))
    | _ => (d, esize, m, n)
  let n : Int := n
  let m : Int := m
  let esize : Int := esize
  let d : Int := d
  let cond : (BitVec 4) :=
    ((cc +++ ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access cc 1)])) ^^^ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
              cc 0)])))) +++ 0#1)
  (execute_aarch32_instrs_VSEL_Op_A_txt cond (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_aarch32_instrs_VSEL_T1enc_A_txt (D : (BitVec 1)) (cc : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := 16
  let d ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3840) 0 31))) ) :
    SailM Nat )
  let n ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3841) 0 31))) ) :
    SailM Nat )
  let m ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3842) 0 31))) ) :
    SailM Nat )
  let (d, esize, m, n) : (Nat × Int × Nat × Nat) :=
    match size with
    | 0b01 =>
      (let esize : Int := 16
      let d : Nat := (BitVec.toNat (Vd +++ D))
      let n : Nat := (BitVec.toNat (Vn +++ N))
      let m : Nat := (BitVec.toNat (Vm +++ M))
      (d, esize, m, n))
    | 0b10 =>
      (let esize : Int := 32
      let d : Nat := (BitVec.toNat (Vd +++ D))
      let n : Nat := (BitVec.toNat (Vn +++ N))
      let m : Nat := (BitVec.toNat (Vm +++ M))
      (d, esize, m, n))
    | 0b11 =>
      (let esize : Int := 64
      let d : Nat := (BitVec.toNat (D +++ Vd))
      let n : Nat := (BitVec.toNat (N +++ Vn))
      let m : Nat := (BitVec.toNat (M +++ Vm))
      (d, esize, m, n))
    | _ => (d, esize, m, n)
  let n : Int := n
  let m : Int := m
  let esize : Int := esize
  let d : Int := d
  let cond : (BitVec 4) :=
    ((cc +++ ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access cc 1)])) ^^^ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
              cc 0)])))) +++ 0#1)
  (execute_aarch32_instrs_VSEL_Op_A_txt cond (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_aarch32_instrs_VDOT_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (U : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveDOTPExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let is_signed : Bool := (U == 0#1)
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let esize : Nat := 32
  let regs : Int :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_VDOT_Op_A_txt (Sail.Int.toNatChecked (d)) esize
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)) is_signed)


def decode_aarch32_instrs_VDOT_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (U : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let w__1 ← (( do (HaveDOTPExt ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let is_signed : Bool := (U == 0#1)
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let esize : Nat := 32
  let regs : Int :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_VDOT_Op_A_txt (Sail.Int.toNatChecked (d)) esize
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)) is_signed)


def decode_aarch32_instrs_VDOT_s_A1enc_A_txt (op1 : (BitVec 1)) (D : (BitVec 1)) (op2 : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (U : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveDOTPExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vn 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let is_signed : Bool := (U == 0#1)
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 3 0))
  let index : Int := (BitVec.toNat M)
  let esize : Nat := 32
  let regs : Int :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_VDOT_s_Op_A_txt (Sail.Int.toNatChecked (d)) esize
    (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)) is_signed)


def decode_aarch32_instrs_VDOT_s_T1enc_A_txt (op1 : (BitVec 1)) (D : (BitVec 1)) (op2 : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (U : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let w__1 ← (( do (HaveDOTPExt ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vn 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let is_signed : Bool := (U == 0#1)
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 3 0))
  let index : Int := (BitVec.toNat M)
  let esize : Nat := 32
  let regs : Int :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_VDOT_s_Op_A_txt (Sail.Int.toNatChecked (d)) esize
    (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)) is_signed)


def decode_aarch32_instrs_VDOT_bf16_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveAArch32BF16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let regs : Int :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_VDOT_bf16_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)))


def decode_aarch32_instrs_VDOT_bf16_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let w__1 ← (( do (HaveAArch32BF16Ext ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let regs : Int :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_VDOT_bf16_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)))


def decode_aarch32_instrs_VDOT_bf16_i_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveAArch32BF16Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vn 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat Vm)
  let i : Int := (BitVec.toNat M)
  let regs : Int :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_VDOT_bf16_i_Op_A_txt (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (i)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)))


def decode_aarch32_instrs_VDOT_bf16_i_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let w__1 ← (( do (HaveAArch32BF16Ext ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vn 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat Vm)
  let i : Int := (BitVec.toNat M)
  let regs : Int :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_VDOT_bf16_i_Op_A_txt (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (i)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)))


def decode_aarch32_instrs_MMLA_A1enc_A_txt (B : (BitVec 1)) (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (U : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveAArch32Int8MatMulExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let op1_unsigned ← (( do (undefined_bool_at (← occLabel 3898) ()) ) : SailM Bool )
  let op2_unsigned ← (( do (undefined_bool_at (← occLabel 3899) ()) ) : SailM Bool )
  let (op1_unsigned, op2_unsigned) ← (( do
    match (BitVec.setWidth 2 (B +++ U)) with
    | 0b00 =>
      (let op1_unsigned : Bool := false
      let op2_unsigned : Bool := false
      (pure ((op1_unsigned, op2_unsigned))))
    | 0b01 =>
      (let op1_unsigned : Bool := true
      let op2_unsigned : Bool := true
      (pure ((op1_unsigned, op2_unsigned))))
    | 0b10 =>
      (let op1_unsigned : Bool := true
      let op2_unsigned : Bool := false
      (pure ((op1_unsigned, op2_unsigned))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × Bool) )
  let op2_unsigned := op2_unsigned
  let op1_unsigned := op1_unsigned
  if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  (execute_aarch32_instrs_MMLA_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned)


def decode_aarch32_instrs_MMLA_T1enc_A_txt (B : (BitVec 1)) (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (U : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let w__1 ← (( do (HaveAArch32Int8MatMulExt ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let op1_unsigned ← (( do (undefined_bool_at (← occLabel 3900) ()) ) : SailM Bool )
  let op2_unsigned ← (( do (undefined_bool_at (← occLabel 3901) ()) ) : SailM Bool )
  let (op1_unsigned, op2_unsigned) ← (( do
    match (BitVec.setWidth 2 (B +++ U)) with
    | 0b00 =>
      (let op1_unsigned : Bool := false
      let op2_unsigned : Bool := false
      (pure ((op1_unsigned, op2_unsigned))))
    | 0b01 =>
      (let op1_unsigned : Bool := true
      let op2_unsigned : Bool := true
      (pure ((op1_unsigned, op2_unsigned))))
    | 0b10 =>
      (let op1_unsigned : Bool := true
      let op2_unsigned : Bool := false
      (pure ((op1_unsigned, op2_unsigned))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × Bool) )
  let op2_unsigned := op2_unsigned
  let op1_unsigned := op1_unsigned
  if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  (execute_aarch32_instrs_MMLA_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned)


def decode_aarch32_instrs_VUSDOT_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveAArch32Int8MatMulExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let regs : Int :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_VUSDOT_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)))


def decode_aarch32_instrs_VUSDOT_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let w__1 ← (( do (HaveAArch32Int8MatMulExt ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let regs : Int :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_VUSDOT_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)))


def decode_aarch32_instrs_DOT_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (U : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveAArch32Int8MatMulExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vn 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let op1_unsigned : Bool := (U == 0#1)
  let op2_unsigned : Bool := (U == 1#1)
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat Vm)
  let i : Int := (BitVec.toNat M)
  let regs : Int :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_DOT_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (i))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
    (Sail.Int.toNatChecked (regs)))


def decode_aarch32_instrs_DOT_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (U : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let w__1 ← (( do (HaveAArch32Int8MatMulExt ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vn 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let op1_unsigned : Bool := (U == 0#1)
  let op2_unsigned : Bool := (U == 1#1)
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat Vm)
  let i : Int := (BitVec.toNat M)
  let regs : Int :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_DOT_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (i))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
    (Sail.Int.toNatChecked (regs)))


def decode_ldg_aarch64_instrs_integer_tags_mcgettag (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Xt)
  let n : Int := (BitVec.toNat Xn)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  (execute_aarch64_instrs_integer_tags_mcgettag (Sail.Int.toNatChecked (n)) offset
    (Sail.Int.toNatChecked (t)))


end ArmFull.Functions
