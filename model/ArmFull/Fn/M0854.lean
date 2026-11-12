import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0024
import ArmFull.Fn.M0043
import ArmFull.Fn.M0044
import ArmFull.Fn.M0045
import ArmFull.Fn.M0046
import ArmFull.Fn.M0049
import ArmFull.Fn.M0051
import ArmFull.Fn.M0063
import ArmFull.Fn.M0086
import ArmFull.Fn.M0114
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0181
import ArmFull.Fn.M0196
import ArmFull.Fn.M0204
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0244
import ArmFull.Fn.M0580
import ArmFull.Fn.M0840
import ArmFull.Fn.M0841
import ArmFull.Fn.M0842

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

def decode_autib_aarch64_instrs_integer_pac_autib_hint (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let d : Int := 17
  let n : Int := 0
  let source_is_sp : Bool := false
  let (d, n, source_is_sp) ← (( do
    match (BitVec.setWidth 7 (CRm +++ op2)) with
    | 0b0011110 =>
      (let d : Int := 30
      let n : Int := 31
      (pure ((d, n, source_is_sp))))
    | 0b0011111 =>
      (let d : Int := 30
      let source_is_sp : Bool := true
      (pure ((d, n, source_is_sp))))
    | 0b0001110 =>
      (let d : Int := 17
      let n : Int := 16
      (pure ((d, n, source_is_sp))))
    | 0b0001000 => sailThrow ((Error_See "PACIA"))
    | 0b0001010 => sailThrow ((Error_See "PACIB"))
    | 0b0001100 => sailThrow ((Error_See "AUTIA"))
    | b__0 =>
      (do
        if (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb b__0 6 1)) == (0b001100#6 : (BitVec 6))) : Bool)
        then sailThrow ((Error_See "PACIA"))
        else
          (do
            if (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb b__0 6 1)) == (0b001101#6 : (BitVec 6))) : Bool)
            then sailThrow ((Error_See "PACIB"))
            else
              (do
                if (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb b__0 6 1)) == (0b001110#6 : (BitVec 6))) : Bool)
                then sailThrow ((Error_See "AUTIA"))
                else
                  (do
                    match b__0 with
                    | 0b0000111 => sailThrow ((Error_See "XPACLRI"))
                    | _ => sailThrow ((Error_See "HINT")))))
        (pure ((d, n, source_is_sp)))) ) : SailM (Int × Int × Bool) )
  let n : Int := n
  let d : Int := d
  ArmFull.assert ((0 ≤b n) && (n ≤b 31)) "armcert/armcert_c27.sail:192.43-192.44"
  (execute_aarch64_instrs_integer_pac_autib_dp_1src (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) source_is_sp)


/-- Type quantifiers: a : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha3_bcax (a : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let Va ← (( do (V_read a 128) ) : SailM (BitVec 128) )
  (V_set d 128 (Vn ^^^ (Vm &&& (Complement.complement Va))))


def execute_aarch64_instrs_system_hints (op : SystemHintOp) : SailM Unit := do
  match op with
  | .SystemHintOp_YIELD => (pure ((Hint_Yield ())))
  | .SystemHintOp_DGH => (pure ((Hint_DGH ())))
  | .SystemHintOp_WFE =>
    (do
      let localtimeout : Int := (Int.shiftl 1 64)
      (Hint_WFE localtimeout WFxType_WFE))
  | .SystemHintOp_WFI =>
    (do
      let localtimeout : Int := (Int.shiftl 1 64)
      (Hint_WFI localtimeout WFxType_WFI))
  | .SystemHintOp_SEV => (pure ((SendEvent ())))
  | .SystemHintOp_SEVL =>
    (do
      (SendEventLocal ()))
  | .SystemHintOp_ESB =>
    (do
      let w__2 ← (( do
        if ((← do
             (HaveTME ())) : Bool)
        then
          (do
            let w__1 ← (( do readReg TSTATE ) : SailM TMState )
            (pure (((w__1.depth >b 0) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          (FailTransaction TMFailure_ERR false))
      else (pure (()))
      let _ : Unit := (SynchronizeErrors ())
      (AArch64_ESBOperation ())
      let w__7 ← (( do
        if ((← do
             if ((← do
                  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__3.EL == EL0) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
                 (pure (((w__4.EL == EL1) : Bool))))) : Bool)
        then
          (do
            (EL2Enabled ()))
        else (pure false) ) : SailM Bool )
      if (w__7 : Bool)
      then
        (do
          (AArch64_vESBOperation ()))
      else (pure (()))
      (TakeUnmaskedSErrorInterrupts ()))
  | .SystemHintOp_PSB => (pure ((ProfilingSynchronizationBarrier ())))
  | .SystemHintOp_TSB => (pure ((TraceSynchronizationBarrier ())))
  | .SystemHintOp_GCSB => (pure ((GCSSynchronizationBarrier ())))
  | .SystemHintOp_CHKFEAT =>
    (do
      let w__8 ← (( do (X_read 16 64) ) : SailM (BitVec 64) )
      let w__9 ← (( do (AArch64_ChkFeat w__8) ) : SailM (BitVec 64) )
      (X_set 16 64 w__9))
  | .SystemHintOp_CSDB =>
    (do
      (ConsumptionOfSpeculativeDataBarrier ()))
  | .SystemHintOp_CLRBHB => (pure ((Hint_CLRBHB ())))
  | .SystemHintOp_BTI =>
    (do
      (SetBTypeNext 0b00#2))
  | .SystemHintOp_NOP => (pure (()))
  | _ =>
    (do
      (Unreachable ()))


/-- Type quantifiers: a : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha3_eor3 (a : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let Va ← (( do (V_read a 128) ) : SailM (BitVec 128) )
  (V_set d 128 ((Vn ^^^ Vm) ^^^ Va))


def decode_eret_aarch64_instrs_branch_unconditional_eret (op4 : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let pac : Bool := (A == 1#1)
  let use_key_a : Bool := (M == 0#1)
  if (((! pac) && (op4 != 0b00000#5)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__3 ← (( do
        if (pac : Bool)
        then
          (do
            (pure ((← do
                  let w__1 ← (( do (HavePACExt ()) ) : SailM Bool )
                  (pure (((! w__1) : Bool)))) || ((op4 != 0b11111#5) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (())))
  if ((Rn != 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_branch_unconditional_eret pac use_key_a)


def decode_ereta_aarch64_instrs_branch_unconditional_eret (op4 : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let pac : Bool := (A == 1#1)
  let use_key_a : Bool := (M == 0#1)
  if (((! pac) && (op4 != 0b00000#5)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__3 ← (( do
        if (pac : Bool)
        then
          (do
            (pure ((← do
                  let w__1 ← (( do (HavePACExt ()) ) : SailM Bool )
                  (pure (((! w__1) : Bool)))) || ((op4 != 0b11111#5) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (())))
  if ((Rn != 0b11111#5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_branch_unconditional_eret pac use_key_a)


/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_move_fp_select (condition : (BitVec 4)) (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPEnabled64 ())
  let w__0 ← (( do (ConditionHolds condition) ) : SailM Bool )
  let result ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (V_read n datasize)))
    else
      (do
        ((Sail.BitVec.castWidth ) <$> (V_read m datasize))) ) : SailM (BitVec datasize) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, List.elem datasize [16, 32, 64] ∧
  0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_move_fp_imm (d : Nat) (datasize : Nat) (imm : (BitVec datasize)) : SailM Unit := do
  (CheckFPEnabled64 ())
  (V_set d datasize (Sail.BitVec.castWidth imm))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha3_rax1 (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let w__0 ← (( do (ROL (Sail.BitVec.extractLsb Vm 127 64) 1) ) : SailM (BitVec 64) )
  let w__1 ← (( do (ROL (Sail.BitVec.extractLsb Vm 63 0) 1) ) : SailM (BitVec 64) )
  (V_set d 128 (Vn ^^^ (w__0 +++ w__1)))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let x ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let y ← (( do (V_read n 32) ) : SailM (BitVec 32) )
  let w ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let t ← (( do (undefined_bitvector_at (← occLabel 4782) 32) ) : SailM (BitVec 32) )
  let (t, x, y) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := 3
    (do
      let mut loop_vars := (t, x, y)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (t, x, y) := loop_vars
        loop_vars ← do
          let t : (BitVec 32) :=
            (SHAchoose (Sail.BitVec.extractLsb x 63 32) (Sail.BitVec.extractLsb x 95 64)
              (Sail.BitVec.extractLsb x 127 96))
          let w__0 ← (( do (ROL (Sail.BitVec.extractLsb x 31 0) 5) ) : SailM (BitVec 32) )
          let w__1 ← (( do (Elem_read w e 32) ) : SailM (BitVec 32) )
          let y := ((((y + w__0) + t) + w__1) : (BitVec 32))
          let w__2 ← (( do (ROL (Sail.BitVec.extractLsb x 63 32) 30) ) : SailM (BitVec 32) )
          let x := ((Sail.BitVec.updateSubrange x 63 32 w__2) : (BitVec 128))
          let split_vec ← (( do (ROL (y +++ x) 32) ) : SailM (BitVec (32 + 128)) )
          let y : (BitVec 32) := (Sail.BitVec.extractLsb split_vec 159 128)
          let x : (BitVec 128) := (Sail.BitVec.extractLsb split_vec 127 0)
          (pure ((t, x, y)))
      (pure loop_vars)) ) : SailM ((BitVec 32) × (BitVec 128) × (BitVec 32)) )
  (V_set d 128 x)


/-- Type quantifiers: d : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha2op_sha1_hash (d : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let operand ← (( do (V_read n 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (ROL operand 30) ) : SailM (BitVec 32) )
  (V_set d 32 w__0)


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let x ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let y ← (( do (V_read n 32) ) : SailM (BitVec 32) )
  let w ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let t ← (( do (undefined_bitvector_at (← occLabel 4783) 32) ) : SailM (BitVec 32) )
  let (t, x, y) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := 3
    (do
      let mut loop_vars := (t, x, y)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (t, x, y) := loop_vars
        loop_vars ← do
          let t : (BitVec 32) :=
            (SHAmajority (Sail.BitVec.extractLsb x 63 32) (Sail.BitVec.extractLsb x 95 64)
              (Sail.BitVec.extractLsb x 127 96))
          let w__0 ← (( do (ROL (Sail.BitVec.extractLsb x 31 0) 5) ) : SailM (BitVec 32) )
          let w__1 ← (( do (Elem_read w e 32) ) : SailM (BitVec 32) )
          let y := ((((y + w__0) + t) + w__1) : (BitVec 32))
          let w__2 ← (( do (ROL (Sail.BitVec.extractLsb x 63 32) 30) ) : SailM (BitVec 32) )
          let x := ((Sail.BitVec.updateSubrange x 63 32 w__2) : (BitVec 128))
          let split_vec ← (( do (ROL (y +++ x) 32) ) : SailM (BitVec (32 + 128)) )
          let y : (BitVec 32) := (Sail.BitVec.extractLsb split_vec 159 128)
          let x : (BitVec 128) := (Sail.BitVec.extractLsb split_vec 127 0)
          (pure ((t, x, y)))
      (pure loop_vars)) ) : SailM ((BitVec 32) × (BitVec 128) × (BitVec 32)) )
  (V_set d 128 x)


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let x ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let y ← (( do (V_read n 32) ) : SailM (BitVec 32) )
  let w ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let t ← (( do (undefined_bitvector_at (← occLabel 4784) 32) ) : SailM (BitVec 32) )
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
          let w__0 ← (( do (ROL (Sail.BitVec.extractLsb x 31 0) 5) ) : SailM (BitVec 32) )
          let w__1 ← (( do (Elem_read w e 32) ) : SailM (BitVec 32) )
          let y := ((((y + w__0) + t) + w__1) : (BitVec 32))
          let w__2 ← (( do (ROL (Sail.BitVec.extractLsb x 63 32) 30) ) : SailM (BitVec 32) )
          let x := ((Sail.BitVec.updateSubrange x 63 32 w__2) : (BitVec 128))
          let split_vec ← (( do (ROL (y +++ x) 32) ) : SailM (BitVec (32 + 128)) )
          let y : (BitVec 32) := (Sail.BitVec.extractLsb split_vec 159 128)
          let x : (BitVec 128) := (Sail.BitVec.extractLsb split_vec 127 0)
          (pure ((t, x, y)))
      (pure loop_vars)) ) : SailM ((BitVec 32) × (BitVec 128) × (BitVec 32)) )
  (V_set d 128 x)


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha3op_sha1_sched0 (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let operand1 ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let operand2 ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let operand3 ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let result : (BitVec 128) :=
    ((Sail.BitVec.extractLsb operand2 63 0) +++ (Sail.BitVec.extractLsb operand1 127 64))
  let result : (BitVec 128) := ((result ^^^ operand1) ^^^ operand3)
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha2op_sha1_sched1 (d : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let operand1 ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let operand2 ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector_at (← occLabel 4785) 128) ) : SailM (BitVec 128) )
  let T : (BitVec 128) := (operand1 ^^^ (operand2 >>> 32))
  let w__0 ← (( do (ROL (Sail.BitVec.extractLsb T 31 0) 1) ) : SailM (BitVec 32) )
  let result := ((Sail.BitVec.updateSubrange result 31 0 w__0) : (BitVec 128))
  let w__1 ← (( do (ROL (Sail.BitVec.extractLsb T 63 32) 1) ) : SailM (BitVec 32) )
  let result := ((Sail.BitVec.updateSubrange result 63 32 w__1) : (BitVec 128))
  let w__2 ← (( do (ROL (Sail.BitVec.extractLsb T 95 64) 1) ) : SailM (BitVec 32) )
  let result := ((Sail.BitVec.updateSubrange result 95 64 w__2) : (BitVec 128))
  let w__3 ← (( do (ROL (Sail.BitVec.extractLsb T 127 96) 1) ) : SailM (BitVec 32) )
  let w__4 ← (( do (ROL (Sail.BitVec.extractLsb T 31 0) 2) ) : SailM (BitVec 32) )
  let result := ((Sail.BitVec.updateSubrange result 127 96 (w__3 ^^^ w__4)) : (BitVec 128))
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_part1 : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha3op_sha256_hash (d : Nat) (m : Nat) (n : Nat) (part1 : Bool) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let result ← (( do (undefined_bitvector_at (← occLabel 4786) 128) ) : SailM (BitVec 128) )
  let result ← (( do
    if (part1 : Bool)
    then
      (do
        let w__0 ← (( do (V_read d 128) ) : SailM (BitVec 128) )
        let w__1 ← (( do (V_read n 128) ) : SailM (BitVec 128) )
        let w__2 ← (( do (V_read m 128) ) : SailM (BitVec 128) )
        (SHA256hash w__0 w__1 w__2 true))
    else
      (do
        let w__4 ← (( do (V_read n 128) ) : SailM (BitVec 128) )
        let w__5 ← (( do (V_read d 128) ) : SailM (BitVec 128) )
        let w__6 ← (( do (V_read m 128) ) : SailM (BitVec 128) )
        (SHA256hash w__4 w__5 w__6 false)) ) : SailM (BitVec 128) )
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha2op_sha256_sched0 (d : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let operand1 ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let operand2 ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector_at (← occLabel 4787) 128) ) : SailM (BitVec 128) )
  let T : (BitVec 128) :=
    ((Sail.BitVec.extractLsb operand2 31 0) +++ (Sail.BitVec.extractLsb operand1 127 32))
  let elt ← (( do (undefined_bitvector_at (← occLabel 4788) 32) ) : SailM (BitVec 32) )
  let (elt, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := 3
    (do
      let mut loop_vars := (elt, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (elt, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Elem_read T e 32) ) : SailM (BitVec 32) )
          let elt := (w__0 : (BitVec 32))
          let elt : (BitVec 32) := (((ROR elt 7) ^^^ (ROR elt 18)) ^^^ (elt >>> 3))
          let w__1 ← (( do (Elem_read operand1 e 32) ) : SailM (BitVec 32) )
          let w__2 ← (( do (Elem_set result e 32 (elt + w__1)) ) : SailM (BitVec 128) )
          let result := (w__2 : (BitVec 128))
          (pure ((elt, result)))
      (pure loop_vars)) ) : SailM ((BitVec 32) × (BitVec 128)) )
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha3op_sha256_sched1 (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let operand1 ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let operand2 ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let operand3 ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector_at (← occLabel 4789) 128) ) : SailM (BitVec 128) )
  let T0 : (BitVec 128) :=
    ((Sail.BitVec.extractLsb operand3 31 0) +++ (Sail.BitVec.extractLsb operand2 127 32))
  let elt ← (( do (undefined_bitvector_at (← occLabel 4790) 32) ) : SailM (BitVec 32) )
  let T1 : (BitVec 64) := (Sail.BitVec.extractLsb operand3 127 64)
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
          let w__1 ← (( do (Elem_read operand1 e 32) ) : SailM (BitVec 32) )
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
          let w__5 ← (( do (Elem_read operand1 e 32) ) : SailM (BitVec 32) )
          let w__6 ← (( do (Elem_read T0 e 32) ) : SailM (BitVec 32) )
          let elt := (((elt + w__5) + w__6) : (BitVec 32))
          let w__7 ← (( do (Elem_set result e 32 elt) ) : SailM (BitVec 128) )
          let result := (w__7 : (BitVec 128))
          (pure ((elt, result)))
      (pure loop_vars)) ) : SailM ((BitVec 32) × (BitVec 128)) )
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha512_sha512h (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vtmp ← (( do (undefined_bitvector_at (← occLabel 4791) 128) ) : SailM (BitVec 128) )
  let x ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let y ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let w ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let MSigma1 : (BitVec 64) :=
    ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (ROR
          (Sail.BitVec.extractLsb y 127 64) 14)) ^^^ (Sail.BitVec.castWidth (m := 64) (ROR
          (Sail.BitVec.extractLsb y 127 64) 18)))) ^^^ (Sail.BitVec.castWidth (m := 64) (ROR
        (Sail.BitVec.extractLsb y 127 64) 41)))
  let Vtmp : (BitVec 128) :=
    (Sail.BitVec.updateSubrange Vtmp 127 64
      ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb y
            127 64)) &&& (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb x 63 0)))) ^^^ (Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.extractLsb y 127 64))) &&& (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb
            x 127 64))))))
  let Vtmp : (BitVec 128) :=
    (Sail.BitVec.updateSubrange Vtmp 127 64
      ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb
            Vtmp 127 64)) + MSigma1)) + (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb w
          127 64))))
  let tmp : (BitVec 64) :=
    ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb Vtmp 127 64)) + (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb
        y 63 0)))
  let MSigma1 : (BitVec 64) := (((ROR tmp 14) ^^^ (ROR tmp 18)) ^^^ (ROR tmp 41))
  let Vtmp : (BitVec 128) :=
    (Sail.BitVec.updateSubrange Vtmp 63 0
      ((Sail.BitVec.castWidth (m := 64) (tmp &&& (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb
            y 127 64)))) ^^^ (Sail.BitVec.castWidth (m := 64) ((Complement.complement tmp) &&& (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb
            x 63 0))))))
  let Vtmp : (BitVec 128) :=
    (Sail.BitVec.updateSubrange Vtmp 63 0
      ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb
            Vtmp 63 0)) + MSigma1)) + (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb w 63
          0))))
  (V_set d 128 Vtmp)


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha512_sha512h2 (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vtmp ← (( do (undefined_bitvector_at (← occLabel 4792) 128) ) : SailM (BitVec 128) )
  let x ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let y ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let w ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let NSigma0 : (BitVec 64) :=
    ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (ROR
          (Sail.BitVec.extractLsb y 63 0) 28)) ^^^ (Sail.BitVec.castWidth (m := 64) (ROR
          (Sail.BitVec.extractLsb y 63 0) 34)))) ^^^ (Sail.BitVec.castWidth (m := 64) (ROR
        (Sail.BitVec.extractLsb y 63 0) 39)))
  let Vtmp : (BitVec 128) :=
    (Sail.BitVec.updateSubrange Vtmp 127 64
      ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb
              x 63 0)) &&& (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb y 127 64)))) ^^^ (Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb
              x 63 0)) &&& (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb y 63 0)))))) ^^^ (Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb
            y 127 64)) &&& (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb y 63 0))))))
  let Vtmp : (BitVec 128) :=
    (Sail.BitVec.updateSubrange Vtmp 127 64
      ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb
            Vtmp 127 64)) + NSigma0)) + (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb w
          127 64))))
  let NSigma0 : (BitVec 64) :=
    ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (ROR
          (Sail.BitVec.extractLsb Vtmp 127 64) 28)) ^^^ (Sail.BitVec.castWidth (m := 64) (ROR
          (Sail.BitVec.extractLsb Vtmp 127 64) 34)))) ^^^ (Sail.BitVec.castWidth (m := 64) (ROR
        (Sail.BitVec.extractLsb Vtmp 127 64) 39)))
  let Vtmp : (BitVec 128) :=
    (Sail.BitVec.updateSubrange Vtmp 63 0
      ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb
              Vtmp 127 64)) &&& (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb y 63 0)))) ^^^ (Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb
              Vtmp 127 64)) &&& (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb y 127 64)))))) ^^^ (Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb
            y 127 64)) &&& (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb y 63 0))))))
  let Vtmp : (BitVec 128) :=
    (Sail.BitVec.updateSubrange Vtmp 63 0
      ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb
            Vtmp 63 0)) + NSigma0)) + (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb w 63
          0))))
  (V_set d 128 Vtmp)


/-- Type quantifiers: d : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha512_sha512su0 (d : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vtmp ← (( do (undefined_bitvector_at (← occLabel 4793) 128) ) : SailM (BitVec 128) )
  let x ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let w ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let sig0 : (BitVec 64) :=
    ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (ROR
          (Sail.BitVec.extractLsb w 127 64) 1)) ^^^ (Sail.BitVec.castWidth (m := 64) (ROR
          (Sail.BitVec.extractLsb w 127 64) 8)))) ^^^ (Sail.BitVec.castWidth (m := 64) (0b0000000#7 +++ (Sail.BitVec.extractLsb
          w 127 71))))
  let Vtmp : (BitVec 128) :=
    (Sail.BitVec.updateSubrange Vtmp 63 0
      ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb w 63 0)) + sig0))
  let sig0 : (BitVec 64) :=
    ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (ROR
          (Sail.BitVec.extractLsb x 63 0) 1)) ^^^ (Sail.BitVec.castWidth (m := 64) (ROR
          (Sail.BitVec.extractLsb x 63 0) 8)))) ^^^ (Sail.BitVec.castWidth (m := 64) (0b0000000#7 +++ (Sail.BitVec.extractLsb
          x 63 7))))
  let Vtmp : (BitVec 128) :=
    (Sail.BitVec.updateSubrange Vtmp 127 64
      ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb w 127 64)) + sig0))
  (V_set d 128 Vtmp)


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha512_sha512su1 (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vtmp ← (( do (undefined_bitvector_at (← occLabel 4794) 128) ) : SailM (BitVec 128) )
  let x ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let y ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let w ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let sig1 : (BitVec 64) :=
    ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (ROR
          (Sail.BitVec.extractLsb x 127 64) 19)) ^^^ (Sail.BitVec.castWidth (m := 64) (ROR
          (Sail.BitVec.extractLsb x 127 64) 61)))) ^^^ (Sail.BitVec.castWidth (m := 64) (0b000000#6 +++ (Sail.BitVec.extractLsb
          x 127 70))))
  let Vtmp : (BitVec 128) :=
    (Sail.BitVec.updateSubrange Vtmp 127 64
      ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb w
            127 64)) + sig1)) + (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb y 127 64))))
  let sig1 : (BitVec 64) :=
    ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (ROR
          (Sail.BitVec.extractLsb x 63 0) 19)) ^^^ (Sail.BitVec.castWidth (m := 64) (ROR
          (Sail.BitVec.extractLsb x 63 0) 61)))) ^^^ (Sail.BitVec.castWidth (m := 64) (0b000000#6 +++ (Sail.BitVec.extractLsb
          x 63 6))))
  let Vtmp : (BitVec 128) :=
    (Sail.BitVec.updateSubrange Vtmp 63 0
      ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb w
            63 0)) + sig1)) + (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.extractLsb y 63 0))))
  (V_set d 128 Vtmp)


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sm3_sm3partw1 (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let Vd ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector_at (← occLabel 4808) 128) ) : SailM (BitVec 128) )
  let w__0 ← (( do (ROL (Sail.BitVec.extractLsb Vm 127 96) 15) ) : SailM (BitVec 32) )
  let w__1 ← (( do (ROL (Sail.BitVec.extractLsb Vm 95 64) 15) ) : SailM (BitVec 32) )
  let w__2 ← (( do (ROL (Sail.BitVec.extractLsb Vm 63 32) 15) ) : SailM (BitVec 32) )
  let result :=
    ((Sail.BitVec.updateSubrange result 95 0
      ((Sail.BitVec.castWidth (m := 96) (Sail.BitVec.extractLsb (Vd ^^^ Vn) 95 0)) ^^^ ((w__0 +++ w__1) +++ w__2))) : (BitVec 128))
  let result ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := 3
    (do
      let mut loop_vars := result
      for i in [loop_i_lower:loop_i_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let result ← (( do
            if ((i == 3) : Bool)
            then
              (do
                let w__3 ← (( do (ROL (Sail.BitVec.extractLsb result 31 0) 15) ) : SailM
                  (BitVec 32) )
                let result :=
                  ((Sail.BitVec.updateSubrange result 127 96
                    ((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb (Vd ^^^ Vn) 127 96)) ^^^ w__3)) : (BitVec 128))
                (pure (result)))
            else (pure (result)) ) : SailM (BitVec 128) )
          let w__4 ← (( do
            ((Sail.BitVec.castWidth ) <$> (ROL
              (Sail.BitVec.extractLsb result (Sail.Int.toNatChecked (((32 *i i) +i 31)))
                (Sail.Int.toNatChecked ((32 *i i)))) 15)) ) : SailM (BitVec 32) )
          let w__5 ← (( do
            ((Sail.BitVec.castWidth ) <$> (ROL
              (Sail.BitVec.extractLsb result (Sail.Int.toNatChecked (((32 *i i) +i 31)))
                (Sail.Int.toNatChecked ((32 *i i)))) 23)) ) : SailM (BitVec 32) )
          let result :=
            ((Sail.BitVec.updateSubrange result (Sail.Int.toNatChecked (((32 *i i) +i 31)))
              (Sail.Int.toNatChecked ((32 *i i)))
              (Sail.BitVec.castWidth ((Sail.BitVec.castWidth (m := 32) ((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                    result (Sail.Int.toNatChecked (((32 *i i) +i 31)))
                    (Sail.Int.toNatChecked ((32 *i i))))) ^^^ w__4)) ^^^ w__5))) : (BitVec 128))
          (pure (result))
      (pure loop_vars)) ) : SailM (BitVec 128) )
  (V_set d 128 result)


end ArmFull.Functions
