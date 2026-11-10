import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0046
import ArmFull.Fn.M0049
import ArmFull.Fn.M0112
import ArmFull.Fn.M0114
import ArmFull.Fn.M0118
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0840
import ArmFull.Fn.M0842
import ArmFull.Fn.M0843

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
def execute_aarch64_instrs_vector_crypto_sm3_sm3partw2 (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let Vd ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector_at (← occLabel 4809) 128) ) : SailM (BitVec 128) )
  let tmp ← (( do (undefined_bitvector_at (← occLabel 4810) 128) ) : SailM (BitVec 128) )
  let w__0 ← (( do (ROL (Sail.BitVec.extractLsb Vm 127 96) 7) ) : SailM (BitVec 32) )
  let w__1 ← (( do (ROL (Sail.BitVec.extractLsb Vm 95 64) 7) ) : SailM (BitVec 32) )
  let w__2 ← (( do (ROL (Sail.BitVec.extractLsb Vm 63 32) 7) ) : SailM (BitVec 32) )
  let w__3 ← (( do (ROL (Sail.BitVec.extractLsb Vm 31 0) 7) ) : SailM (BitVec 32) )
  let tmp :=
    ((Sail.BitVec.updateSubrange tmp 127 0 (Vn ^^^ (((w__0 +++ w__1) +++ w__2) +++ w__3))) : (BitVec 128))
  let result : (BitVec 128) :=
    (Sail.BitVec.updateSubrange result 127 0
      ((Sail.BitVec.castWidth (m := 128) (Sail.BitVec.extractLsb Vd 127 0)) ^^^ (Sail.BitVec.castWidth (m := 128) (Sail.BitVec.extractLsb
          tmp 127 0))))
  let tmp2 ← (( do (ROL (Sail.BitVec.extractLsb tmp 31 0) 15) ) : SailM (BitVec 32) )
  let w__4 ← (( do (ROL tmp2 15) ) : SailM (BitVec 32) )
  let w__5 ← (( do (ROL tmp2 23) ) : SailM (BitVec 32) )
  let tmp2 : (BitVec 32) := ((tmp2 ^^^ w__4) ^^^ w__5)
  let result : (BitVec 128) :=
    (Sail.BitVec.updateSubrange result 127 96
      ((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb result 127 96)) ^^^ tmp2))
  (V_set d 128 result)


/-- Type quantifiers: a : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sm3_sm3ss1 (a : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let Va ← (( do (V_read a 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector_at (← occLabel 4811) 128) ) : SailM (BitVec 128) )
  let w__0 ← (( do (ROL (Sail.BitVec.extractLsb Vn 127 96) 12) ) : SailM (BitVec 32) )
  let w__1 ← (( do
    (ROL
      ((Sail.BitVec.castWidth (m := 32) (w__0 + (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
            Vm 127 96)))) + (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb Va 127 96))) 7)
    ) : SailM (BitVec 32) )
  let result := ((Sail.BitVec.updateSubrange result 127 96 w__1) : (BitVec 128))
  let result : (BitVec 128) := (Sail.BitVec.updateSubrange result 95 0 (Zeros (n := 96)))
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, i : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem i [0, 1, 2, 3] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sm3_sm3tt1a (d : Nat) (i : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let Vd ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector_at (← occLabel 4812) 128) ) : SailM (BitVec 128) )
  let WjPrime ← (( do (Elem_read Vm i 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (ROL (Sail.BitVec.extractLsb Vd 127 96) 12) ) : SailM (BitVec 32) )
  let SS2 : (BitVec 32) :=
    ((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb Vn 127 96)) ^^^ w__0)
  let TT1 : (BitVec 32) :=
    ((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb Vd 63 32)) ^^^ (Sail.BitVec.castWidth (m := 32) ((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
          Vd 127 96)) ^^^ (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb Vd 95 64)))))
  let TT1 : (BitVec 32) :=
    (Sail.BitVec.extractLsb
      ((Sail.BitVec.castWidth (m := 32) ((Sail.BitVec.castWidth (m := 32) (TT1 + (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
              Vd 31 0)))) + SS2)) + WjPrime) 31 0)
  let result : (BitVec 128) :=
    (Sail.BitVec.updateSubrange result 31 0 (Sail.BitVec.extractLsb Vd 63 32))
  let w__1 ← (( do (ROL (Sail.BitVec.extractLsb Vd 95 64) 9) ) : SailM (BitVec 32) )
  let result := ((Sail.BitVec.updateSubrange result 63 32 w__1) : (BitVec 128))
  let result : (BitVec 128) :=
    (Sail.BitVec.updateSubrange result 95 64 (Sail.BitVec.extractLsb Vd 127 96))
  let result : (BitVec 128) := (Sail.BitVec.updateSubrange result 127 96 TT1)
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, i : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem i [0, 1, 2, 3] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sm3_sm3tt1b (d : Nat) (i : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let Vd ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector_at (← occLabel 4813) 128) ) : SailM (BitVec 128) )
  let WjPrime ← (( do (Elem_read Vm i 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (ROL (Sail.BitVec.extractLsb Vd 127 96) 12) ) : SailM (BitVec 32) )
  let SS2 : (BitVec 32) :=
    ((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb Vn 127 96)) ^^^ w__0)
  let TT1 : (BitVec 32) :=
    ((Sail.BitVec.castWidth (m := 32) ((Sail.BitVec.castWidth (m := 32) ((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
            Vd 127 96)) &&& (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb Vd 63 32)))) ||| (Sail.BitVec.castWidth (m := 32) ((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
            Vd 127 96)) &&& (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb Vd 95 64)))))) ||| (Sail.BitVec.castWidth (m := 32) ((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
          Vd 63 32)) &&& (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb Vd 95 64)))))
  let TT1 : (BitVec 32) :=
    (Sail.BitVec.extractLsb
      ((Sail.BitVec.castWidth (m := 32) ((Sail.BitVec.castWidth (m := 32) (TT1 + (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
              Vd 31 0)))) + SS2)) + WjPrime) 31 0)
  let result : (BitVec 128) :=
    (Sail.BitVec.updateSubrange result 31 0 (Sail.BitVec.extractLsb Vd 63 32))
  let w__1 ← (( do (ROL (Sail.BitVec.extractLsb Vd 95 64) 9) ) : SailM (BitVec 32) )
  let result := ((Sail.BitVec.updateSubrange result 63 32 w__1) : (BitVec 128))
  let result : (BitVec 128) :=
    (Sail.BitVec.updateSubrange result 95 64 (Sail.BitVec.extractLsb Vd 127 96))
  let result : (BitVec 128) := (Sail.BitVec.updateSubrange result 127 96 TT1)
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, i : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem i [0, 1, 2, 3] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sm3_sm3tt2a (d : Nat) (i : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let Vd ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector_at (← occLabel 4814) 128) ) : SailM (BitVec 128) )
  let Wj ← (( do (Elem_read Vm i 32) ) : SailM (BitVec 32) )
  let TT2 : (BitVec 32) :=
    ((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb Vd 63 32)) ^^^ (Sail.BitVec.castWidth (m := 32) ((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
          Vd 127 96)) ^^^ (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb Vd 95 64)))))
  let TT2 : (BitVec 32) :=
    (Sail.BitVec.extractLsb
      ((Sail.BitVec.castWidth (m := 32) ((Sail.BitVec.castWidth (m := 32) (TT2 + (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
              Vd 31 0)))) + (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb Vn 127 96)))) + Wj)
      31 0)
  let result : (BitVec 128) :=
    (Sail.BitVec.updateSubrange result 31 0 (Sail.BitVec.extractLsb Vd 63 32))
  let w__0 ← (( do (ROL (Sail.BitVec.extractLsb Vd 95 64) 19) ) : SailM (BitVec 32) )
  let result := ((Sail.BitVec.updateSubrange result 63 32 w__0) : (BitVec 128))
  let result : (BitVec 128) :=
    (Sail.BitVec.updateSubrange result 95 64 (Sail.BitVec.extractLsb Vd 127 96))
  let w__1 ← (( do (ROL TT2 9) ) : SailM (BitVec 32) )
  let w__2 ← (( do (ROL TT2 17) ) : SailM (BitVec 32) )
  let result :=
    ((Sail.BitVec.updateSubrange result 127 96 ((TT2 ^^^ w__1) ^^^ w__2)) : (BitVec 128))
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, i : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem i [0, 1, 2, 3] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sm3_sm3tt2b (d : Nat) (i : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let Vd ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector_at (← occLabel 4815) 128) ) : SailM (BitVec 128) )
  let Wj ← (( do (Elem_read Vm i 32) ) : SailM (BitVec 32) )
  let TT2 : (BitVec 32) :=
    ((Sail.BitVec.castWidth (m := 32) ((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb Vd
          127 96)) &&& (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb Vd 95 64)))) ||| (Sail.BitVec.castWidth (m := 32) ((Sail.BitVec.castWidth (m := 32) (Complement.complement
          (Sail.BitVec.extractLsb Vd 127 96))) &&& (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
          Vd 63 32)))))
  let TT2 : (BitVec 32) :=
    (Sail.BitVec.extractLsb
      ((Sail.BitVec.castWidth (m := 32) ((Sail.BitVec.castWidth (m := 32) (TT2 + (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
              Vd 31 0)))) + (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb Vn 127 96)))) + Wj)
      31 0)
  let result : (BitVec 128) :=
    (Sail.BitVec.updateSubrange result 31 0 (Sail.BitVec.extractLsb Vd 63 32))
  let w__0 ← (( do (ROL (Sail.BitVec.extractLsb Vd 95 64) 19) ) : SailM (BitVec 32) )
  let result := ((Sail.BitVec.updateSubrange result 63 32 w__0) : (BitVec 128))
  let result : (BitVec 128) :=
    (Sail.BitVec.updateSubrange result 95 64 (Sail.BitVec.extractLsb Vd 127 96))
  let w__1 ← (( do (ROL TT2 9) ) : SailM (BitVec 32) )
  let w__2 ← (( do (ROL TT2 17) ) : SailM (BitVec 32) )
  let result :=
    ((Sail.BitVec.updateSubrange result 127 96 ((TT2 ^^^ w__1) ^^^ w__2)) : (BitVec 128))
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sm4_sm4enc (d : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let intval ← (( do (undefined_bitvector_at (← occLabel 4816) 32) ) : SailM (BitVec 32) )
  let roundkey ← (( do (undefined_bitvector_at (← occLabel 4817) 32) ) : SailM (BitVec 32) )
  let roundresult ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let (intval, roundkey, roundresult) ← (( do
    let loop_index_lower : Nat := 0
    let loop_index_upper : Nat := 3
    (do
      let mut loop_vars := (intval, roundkey, roundresult)
      for index in [loop_index_lower:loop_index_upper:1]i do
        let (intval, roundkey, roundresult) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Elem_read Vn index 32) ) : SailM (BitVec 32) )
          let roundkey := (w__0 : (BitVec 32))
          let intval : (BitVec 32) :=
            ((Sail.BitVec.castWidth (m := 32) ((Sail.BitVec.castWidth (m := 32) ((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                    roundresult 127 96)) ^^^ (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                    roundresult 95 64)))) ^^^ (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                  roundresult 63 32)))) ^^^ roundkey)
          let intval ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 3
            (do
              let mut loop_vars_1 := intval
              for i in [loop_i_lower:loop_i_upper:1]i do
                let intval := loop_vars_1
                loop_vars_1 ← do
                  let w__1 ← (( do (Elem_read intval i 8) ) : SailM (BitVec 8) )
                  (Elem_set intval i 8 (Sbox w__1))
              (pure loop_vars_1)) ) : SailM (BitVec 32) )
          let w__3 ← (( do (ROL intval 2) ) : SailM (BitVec 32) )
          let w__4 ← (( do (ROL intval 10) ) : SailM (BitVec 32) )
          let w__5 ← (( do (ROL intval 18) ) : SailM (BitVec 32) )
          let w__6 ← (( do (ROL intval 24) ) : SailM (BitVec 32) )
          let intval := (((((intval ^^^ w__3) ^^^ w__4) ^^^ w__5) ^^^ w__6) : (BitVec 32))
          let intval : (BitVec 32) :=
            (intval ^^^ (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb roundresult 31 0)))
          let roundresult : (BitVec 128) :=
            (Sail.BitVec.updateSubrange roundresult 31 0 (Sail.BitVec.extractLsb roundresult 63 32))
          let roundresult : (BitVec 128) :=
            (Sail.BitVec.updateSubrange roundresult 63 32 (Sail.BitVec.extractLsb roundresult 95 64))
          let roundresult : (BitVec 128) :=
            (Sail.BitVec.updateSubrange roundresult 95 64
              (Sail.BitVec.extractLsb roundresult 127 96))
          let roundresult : (BitVec 128) := (Sail.BitVec.updateSubrange roundresult 127 96 intval)
          (pure ((intval, roundkey, roundresult)))
      (pure loop_vars)) ) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 128)) )
  (V_set d 128 roundresult)


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sm4_sm4enckey (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let intval ← (( do (undefined_bitvector_at (← occLabel 4818) 32) ) : SailM (BitVec 32) )
  let const ← (( do (undefined_bitvector_at (← occLabel 4819) 32) ) : SailM (BitVec 32) )
  let roundresult ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let (const, intval, roundresult) ← (( do
    let loop_index_lower : Nat := 0
    let loop_index_upper : Nat := 3
    (do
      let mut loop_vars := (const, intval, roundresult)
      for index in [loop_index_lower:loop_index_upper:1]i do
        let (const, intval, roundresult) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Elem_read Vm index 32) ) : SailM (BitVec 32) )
          let const := (w__0 : (BitVec 32))
          let intval : (BitVec 32) :=
            ((Sail.BitVec.castWidth (m := 32) ((Sail.BitVec.castWidth (m := 32) ((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                    roundresult 127 96)) ^^^ (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                    roundresult 95 64)))) ^^^ (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                  roundresult 63 32)))) ^^^ const)
          let intval ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 3
            (do
              let mut loop_vars_1 := intval
              for i in [loop_i_lower:loop_i_upper:1]i do
                let intval := loop_vars_1
                loop_vars_1 ← do
                  let w__1 ← (( do (Elem_read intval i 8) ) : SailM (BitVec 8) )
                  (Elem_set intval i 8 (Sbox w__1))
              (pure loop_vars_1)) ) : SailM (BitVec 32) )
          let w__3 ← (( do (ROL intval 13) ) : SailM (BitVec 32) )
          let w__4 ← (( do (ROL intval 23) ) : SailM (BitVec 32) )
          let intval := (((intval ^^^ w__3) ^^^ w__4) : (BitVec 32))
          let intval : (BitVec 32) :=
            (intval ^^^ (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb roundresult 31 0)))
          let roundresult : (BitVec 128) :=
            (Sail.BitVec.updateSubrange roundresult 31 0 (Sail.BitVec.extractLsb roundresult 63 32))
          let roundresult : (BitVec 128) :=
            (Sail.BitVec.updateSubrange roundresult 63 32 (Sail.BitVec.extractLsb roundresult 95 64))
          let roundresult : (BitVec 128) :=
            (Sail.BitVec.updateSubrange roundresult 95 64
              (Sail.BitVec.extractLsb roundresult 127 96))
          let roundresult : (BitVec 128) := (Sail.BitVec.updateSubrange roundresult 127 96 intval)
          (pure ((const, intval, roundresult)))
      (pure loop_vars)) ) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 128)) )
  (V_set d 128 roundresult)


/-- Type quantifiers: sys_crm : Nat, sys_crn : Nat, sys_op0 : Nat, sys_op1 : Nat, sys_op2 : Nat, t :
  Nat, t2 : Nat, 1 ≤ t2 ∧
  t2 ≤ 32 ∧
  0 ≤ t ∧
  t ≤ 31 ∧
  List.elem sys_op2 [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem sys_op1 [0, 1, 2, 3, 4, 5, 6, 7] ∧
  sys_op0 = 1 ∧ 0 ≤ sys_crn ∧ sys_crn ≤ 15 ∧ 0 ≤ sys_crm ∧ sys_crm ≤ 15 -/
def execute_aarch64_instrs_system_sysops_128 (sys_crm : Nat) (sys_crn : Nat) (sys_op0 : Nat) (sys_op1 : Nat) (sys_op2 : Nat) (t : Nat) (t2 : Nat) : SailM Unit := do
  (AArch64_SysInstr128 sys_op0 sys_op1 sys_crn sys_crm sys_op2 t t2)


def decode_wfet_aarch64_instrs_system_sysinstwithreg_wfet (Rd : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatWFxT ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  (execute_aarch64_instrs_system_sysinstwithreg_wfet (Sail.Int.toNatChecked (d)))


def decode_wfit_aarch64_instrs_system_sysinstwithreg_wfit (Rd : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatWFxT ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  (execute_aarch64_instrs_system_sysinstwithreg_wfit (Sail.Int.toNatChecked (d)))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha3_xar (d : Nat) (imm6 : (BitVec 6)) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let tmp : (BitVec 128) := (Vn ^^^ Vm)
  (V_set d 128
    ((ROR (Sail.BitVec.extractLsb tmp 127 64) (BitVec.toNat imm6)) +++ (ROR
        (Sail.BitVec.extractLsb tmp 63 0) (BitVec.toNat imm6))))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Int, List.elem esize [8, 16, 32, 64]
  ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_ADD_Z_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5192)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
            SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth (BitVec.addInt element1 imm)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Int, List.elem esize [8, 16, 32, 64]
  ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SUB_Z_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5193)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
            SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth (BitVec.subInt element1 imm)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Int, List.elem esize [8, 16, 32, 64]
  ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SUBR_Z_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5194)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 : Int := (BitVec.toNat w__0)
          (Elem_set result e esize
            (Sail.BitVec.castWidth (integer_subrange (imm -i element1) (esize -i 1) 0)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Int, List.elem esize [8, 16, 32, 64]
  ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_MUL_Z_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5195)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 : Int := (BitVec.toInt w__0)
          (Elem_set result e esize
            (Sail.BitVec.castWidth (integer_subrange (element1 *i imm) (esize -i 1) 0)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Int, k_is_unsigned : Bool, List.elem
  esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UMAX_Z_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Int) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5196)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          (Elem_set result e esize
            (Sail.BitVec.castWidth (integer_subrange (Max.max element1 imm) (esize -i 1) 0)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Int, k_is_unsigned : Bool, List.elem
  esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SMAX_Z_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Int) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5197)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          (Elem_set result e esize
            (Sail.BitVec.castWidth (integer_subrange (Max.max element1 imm) (esize -i 1) 0)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Int, k_is_unsigned : Bool, List.elem
  esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UMIN_Z_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Int) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5198)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          (Elem_set result e esize
            (Sail.BitVec.castWidth (integer_subrange (Min.min element1 imm) (esize -i 1) 0)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Int, k_is_unsigned : Bool, List.elem
  esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SMIN_Z_ZI__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Int) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5199)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          (Elem_set result e esize
            (Sail.BitVec.castWidth (integer_subrange (Min.min element1 imm) (esize -i 1) 0)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, imm : Int, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ADDPL_R_RI__ (VL : Nat) (d : Nat) (imm : Int) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let operand1 ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let result : (BitVec 64) := (BitVec.addInt operand1 (imm *i (Int.ediv PL 8)))
  if ((d == 31) : Bool)
  then
    (do
      (SP_set result))
  else
    (do
      (X_set d 64 result))


/-- Type quantifiers: VL : Nat, d : Nat, imm : Int, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ADDVL_R_RI__ (VL : Nat) (d : Nat) (imm : Int) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let operand1 ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let result : (BitVec 64) := (BitVec.addInt operand1 (imm *i (Int.ediv VL 8)))
  if ((d == 31) : Bool)
  then
    (do
      (SP_set result))
  else
    (do
      (X_set d 64 result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ADD_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5200)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
            SailM (BitVec esize) )
          let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
            SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth (element1 + element2)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_AND_Z_ZZ__ (VL : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth (operand1 &&& operand2)))


/-- Type quantifiers: VL : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BIC_Z_ZZ__ (VL : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth (operand1 &&& (Complement.complement operand2))))


end ArmFull.Functions
