import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0041
import ArmFull.Fn.M0043
import ArmFull.Fn.M0046
import ArmFull.Fn.M0063
import ArmFull.Fn.M0082
import ArmFull.Fn.M0086
import ArmFull.Fn.M0115
import ArmFull.Fn.M0121
import ArmFull.Fn.M0124
import ArmFull.Fn.M0144
import ArmFull.Fn.M0159
import ArmFull.Fn.M0175
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0185
import ArmFull.Fn.M0195
import ArmFull.Fn.M0197
import ArmFull.Fn.M0200
import ArmFull.Fn.M0201
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203
import ArmFull.Fn.M0228
import ArmFull.Fn.M0244
import ArmFull.Fn.M0253
import ArmFull.Fn.M0254
import ArmFull.Fn.M0255

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

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SBC_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 3208) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3209) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let shifted ← (( do (Shift w__0 shift_t shift_n w__1.C) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  let (tup__0, tup__1) :=
    ((AddWithCarry w__2 (Complement.complement shifted) w__3.C) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__4 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__5 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__6 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__7 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure (())))


/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SUB_i_Op_A_txt (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 3276) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3277) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let (tup__0, tup__1) :=
    ((AddWithCarry w__0 (Complement.complement imm32) 1#1) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__1 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__2 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__3 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__4 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure (())))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SUB_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 3278) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3279) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let shifted ← (( do (Shift w__0 shift_t shift_n w__1.C) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let (tup__0, tup__1) :=
    ((AddWithCarry w__2 (Complement.complement shifted) 1#1) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__3 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__4 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__5 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__6 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure (())))


/-- Type quantifiers: d : Nat, k_setflags : Bool, 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SUB_SP_i_Op_A_txt (d : Nat) (imm32 : (BitVec 32)) (setflags : Bool) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 3288) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3289) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read 13) ) : SailM (BitVec 32) )
  let (tup__0, tup__1) :=
    ((AddWithCarry w__0 (Complement.complement imm32) 1#1) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__1 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__2 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__3 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__4 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure (())))


/-- Type quantifiers: d : Nat, m : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ m ∧
  m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SUB_SP_r_Op_A_txt (d : Nat) (m : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 3290) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3291) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let shifted ← (( do (Shift w__0 shift_t shift_n w__1.C) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read 13) ) : SailM (BitVec 32) )
  let (tup__0, tup__1) :=
    ((AddWithCarry w__2 (Complement.complement shifted) 1#1) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__3 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__4 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__5 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__6 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure (())))


def decode_aarch32_instrs_ERET_A1enc_A_txt (cond : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:40855.29-40855.30"
      (execute_aarch32_instrs_ERET_Op_AS_txt ()))
  else (pure (()))


def decode_aarch32_instrs_ERET_T1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__3 ← (( do
        if ((← do
             (InITBlock ())) : Bool)
        then
          (do
            let w__2 ← (( do (LastInITBlock ()) ) : SailM Bool )
            (pure (((! w__2) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_ERET_Op_AS_txt ()))
  else (pure (()))


/-- Type quantifiers: d : Nat, k_read_spsr : Bool, 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_MRS_br_Op_AS_txt (SYSm : (BitVec 5)) (d : Nat) (read_spsr : Bool) : SailM Unit := do
  let mode ← (( do (undefined_bitvector_at (← occLabel 3783) 5) ) : SailM (BitVec 5) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.EL == EL0) : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let mode : (BitVec 5) := w__1.M
      if (read_spsr : Bool)
      then
        (do
          (SPSRaccessValid SYSm mode)
          match SYSm with
          | 0b01110 =>
            (do
              let w__2 ← (( do readReg SPSR_fiq ) : SailM (BitVec 64) )
              (R_set d (Sail.BitVec.extractLsb w__2 31 0)))
          | 0b10000 =>
            (do
              let w__3 ← (( do readReg SPSR_irq ) : SailM (BitVec 64) )
              (R_set d (Sail.BitVec.extractLsb w__3 31 0)))
          | 0b10010 =>
            (do
              let w__4 ← (( do (SPSR_svc_read ()) ) : SailM (BitVec 32) )
              (R_set d (Sail.BitVec.extractLsb w__4 31 0)))
          | 0b10100 =>
            (do
              let w__5 ← (( do readReg SPSR_abt ) : SailM (BitVec 64) )
              (R_set d (Sail.BitVec.extractLsb w__5 31 0)))
          | 0b10110 =>
            (do
              let w__6 ← (( do readReg SPSR_und ) : SailM (BitVec 64) )
              (R_set d (Sail.BitVec.extractLsb w__6 31 0)))
          | 0b11100 =>
            (do
              let w__7 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
              if ((! w__7) : Bool)
              then
                (do
                  (AArch64_MonitorModeTrap ()))
              else (pure (()))
              let w__8 ← (( do readReg SPSR_mon ) : SailM (BitVec 32) )
              (R_set d w__8))
          | 0b11110 =>
            (do
              let w__9 ← (( do (SPSR_hyp_read ()) ) : SailM (BitVec 32) )
              (R_set d (Sail.BitVec.extractLsb w__9 31 0)))
          | _ => (pure (())))
      else
        (do
          let m ← (( do (undefined_int_at (← occLabel 3784) ()) ) : SailM Int )
          (BankedRegisterAccessValid SYSm mode)
          let b__0 := SYSm
          if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b00#2 : (BitVec 2))) : Bool)
          then
            (do
              let m : Int := ((BitVec.toNat (Sail.BitVec.extractLsb SYSm 2 0)) +i 8)
              let w__10 ← (( do (Rmode_read m M32_User) ) : SailM (BitVec 32) )
              (R_set d w__10))
          else
            (do
              if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b01#2 : (BitVec 2))) : Bool)
              then
                (do
                  let m : Int := ((BitVec.toNat (Sail.BitVec.extractLsb SYSm 2 0)) +i 8)
                  let w__11 ← (( do (Rmode_read m M32_FIQ) ) : SailM (BitVec 32) )
                  (R_set d w__11))
              else
                (do
                  if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 4 1)) == (0x8#4 : (BitVec 4))) : Bool)
                  then
                    (do
                      let m : Int :=
                        (14 -i (BitVec.toNat
                            (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access SYSm 0)]))))
                      let w__12 ← (( do (Rmode_read m M32_IRQ) ) : SailM (BitVec 32) )
                      (R_set d w__12))
                  else
                    (do
                      if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 4 1)) == (0x9#4 : (BitVec 4))) : Bool)
                      then
                        (do
                          let m : Int :=
                            (14 -i (BitVec.toNat
                                (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access SYSm 0)]))))
                          let w__13 ← (( do (Rmode_read m M32_Svc) ) : SailM (BitVec 32) )
                          (R_set d w__13))
                      else
                        (do
                          if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 4 1)) == (0xA#4 : (BitVec 4))) : Bool)
                          then
                            (do
                              let m : Int :=
                                (14 -i (BitVec.toNat
                                    (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access SYSm 0)]))))
                              let w__14 ← (( do (Rmode_read m M32_Abort) ) : SailM (BitVec 32) )
                              (R_set d w__14))
                          else
                            (do
                              if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 4 1)) == (0xB#4 : (BitVec 4))) : Bool)
                              then
                                (do
                                  let m : Int :=
                                    (14 -i (BitVec.toNat
                                        (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access SYSm 0)]))))
                                  let w__15 ← (( do (Rmode_read m M32_Undef) ) : SailM (BitVec 32)
                                    )
                                  (R_set d w__15))
                              else
                                (do
                                  if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0
                                         4 1)) == (0xE#4 : (BitVec 4))) : Bool)
                                  then
                                    (do
                                      let w__16 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      if ((! w__16) : Bool)
                                      then
                                        (do
                                          (AArch64_MonitorModeTrap ()))
                                      else (pure (()))
                                      let m : Int :=
                                        (14 -i (BitVec.toNat
                                            (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access SYSm 0)]))))
                                      let w__17 ← (( do (Rmode_read m M32_Monitor) ) : SailM
                                        (BitVec 32) )
                                      (R_set d w__17))
                                  else
                                    (do
                                      match b__0 with
                                      | 0b11110 =>
                                        (do
                                          let w__18 ← (( do (ELR_hyp_read ()) ) : SailM
                                            (BitVec 32) )
                                          (R_set d w__18))
                                      | 0b11111 =>
                                        (do
                                          let w__19 ← (( do (Rmode_read 13 M32_Hyp) ) : SailM
                                            (BitVec 32) )
                                          (R_set d w__19))
                                      | _ => (pure (())))))))))))


/-- Type quantifiers: n : Nat, k_write_spsr : Bool, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_MSR_br_Op_AS_txt (SYSm : (BitVec 5)) (n : Nat) (write_spsr : Bool) : SailM Unit := do
  let mode ← (( do (undefined_bitvector_at (← occLabel 3785) 5) ) : SailM (BitVec 5) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.EL == EL0) : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let mode : (BitVec 5) := w__1.M
      if (write_spsr : Bool)
      then
        (do
          (SPSRaccessValid SYSm mode)
          match SYSm with
          | 0b01110 =>
            (do
              let w__2 ← (( do readReg SPSR_fiq ) : SailM (BitVec 64) )
              let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
              writeReg SPSR_fiq (Sail.BitVec.updateSubrange w__2 31 0 w__3))
          | 0b10000 =>
            (do
              let w__4 ← (( do readReg SPSR_irq ) : SailM (BitVec 64) )
              let w__5 ← (( do (R_read n) ) : SailM (BitVec 32) )
              writeReg SPSR_irq (Sail.BitVec.updateSubrange w__4 31 0 w__5))
          | 0b10010 =>
            (do
              let w__6 ← (( do (SPSR_svc_read ()) ) : SailM (BitVec 32) )
              let w__7 ← (( do (R_read n) ) : SailM (BitVec 32) )
              (SPSR_svc_write (Mk_SPSR_svc_Type (Sail.BitVec.updateSubrange w__6 31 0 w__7))))
          | 0b10100 =>
            (do
              let w__8 ← (( do readReg SPSR_abt ) : SailM (BitVec 64) )
              let w__9 ← (( do (R_read n) ) : SailM (BitVec 32) )
              writeReg SPSR_abt (Sail.BitVec.updateSubrange w__8 31 0 w__9))
          | 0b10110 =>
            (do
              let w__10 ← (( do readReg SPSR_und ) : SailM (BitVec 64) )
              let w__11 ← (( do (R_read n) ) : SailM (BitVec 32) )
              writeReg SPSR_und (Sail.BitVec.updateSubrange w__10 31 0 w__11))
          | 0b11100 =>
            (do
              let w__12 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
              if ((! w__12) : Bool)
              then
                (do
                  (AArch64_MonitorModeTrap ()))
              else (pure (()))
              let w__13 ← (( do readReg SPSR_mon ) : SailM (BitVec 32) )
              let w__14 ← (( do (R_read n) ) : SailM (BitVec 32) )
              writeReg SPSR_mon (Sail.BitVec.updateSubrange w__13 31 0 w__14))
          | 0b11110 =>
            (do
              let w__15 ← (( do (SPSR_hyp_read ()) ) : SailM (BitVec 32) )
              let w__16 ← (( do (R_read n) ) : SailM (BitVec 32) )
              (SPSR_hyp_write (Mk_SPSR_hyp_Type (Sail.BitVec.updateSubrange w__15 31 0 w__16))))
          | _ => (pure (())))
      else
        (do
          let m ← (( do (undefined_int_at (← occLabel 3786) ()) ) : SailM Int )
          (BankedRegisterAccessValid SYSm mode)
          let b__0 := SYSm
          if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b00#2 : (BitVec 2))) : Bool)
          then
            (do
              let m : Int := ((BitVec.toNat (Sail.BitVec.extractLsb SYSm 2 0)) +i 8)
              let w__17 ← (( do (R_read n) ) : SailM (BitVec 32) )
              (Rmode_set m M32_User w__17))
          else
            (do
              if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b01#2 : (BitVec 2))) : Bool)
              then
                (do
                  let m : Int := ((BitVec.toNat (Sail.BitVec.extractLsb SYSm 2 0)) +i 8)
                  let w__18 ← (( do (R_read n) ) : SailM (BitVec 32) )
                  (Rmode_set m M32_FIQ w__18))
              else
                (do
                  if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 4 1)) == (0x8#4 : (BitVec 4))) : Bool)
                  then
                    (do
                      let m : Int :=
                        (14 -i (BitVec.toNat
                            (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access SYSm 0)]))))
                      let w__19 ← (( do (R_read n) ) : SailM (BitVec 32) )
                      (Rmode_set m M32_IRQ w__19))
                  else
                    (do
                      if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 4 1)) == (0x9#4 : (BitVec 4))) : Bool)
                      then
                        (do
                          let m : Int :=
                            (14 -i (BitVec.toNat
                                (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access SYSm 0)]))))
                          let w__20 ← (( do (R_read n) ) : SailM (BitVec 32) )
                          (Rmode_set m M32_Svc w__20))
                      else
                        (do
                          if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 4 1)) == (0xA#4 : (BitVec 4))) : Bool)
                          then
                            (do
                              let m : Int :=
                                (14 -i (BitVec.toNat
                                    (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access SYSm 0)]))))
                              let w__21 ← (( do (R_read n) ) : SailM (BitVec 32) )
                              (Rmode_set m M32_Abort w__21))
                          else
                            (do
                              if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 4 1)) == (0xB#4 : (BitVec 4))) : Bool)
                              then
                                (do
                                  let m : Int :=
                                    (14 -i (BitVec.toNat
                                        (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access SYSm 0)]))))
                                  let w__22 ← (( do (R_read n) ) : SailM (BitVec 32) )
                                  (Rmode_set m M32_Undef w__22))
                              else
                                (do
                                  if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0
                                         4 1)) == (0xE#4 : (BitVec 4))) : Bool)
                                  then
                                    (do
                                      let w__23 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      if ((! w__23) : Bool)
                                      then
                                        (do
                                          (AArch64_MonitorModeTrap ()))
                                      else (pure (()))
                                      let m : Int :=
                                        (14 -i (BitVec.toNat
                                            (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access SYSm 0)]))))
                                      let w__24 ← (( do (R_read n) ) : SailM (BitVec 32) )
                                      (Rmode_set m M32_Monitor w__24))
                                  else
                                    (do
                                      match b__0 with
                                      | 0b11110 =>
                                        (do
                                          let w__25 ← (( do (R_read n) ) : SailM (BitVec 32) )
                                          (ELR_hyp_write w__25))
                                      | 0b11111 =>
                                        (do
                                          let w__26 ← (( do (R_read n) ) : SailM (BitVec 32) )
                                          (Rmode_set 13 M32_Hyp w__26))
                                      | _ => (pure (())))))))))))


def execute_aarch64_instrs_system_exceptions_debug_breakpoint (comment : (BitVec 16)) : SailM Unit := do
  (AArch64_SoftwareBreakpoint comment)


def execute_aarch64_instrs_system_exceptions_runtime_hvc (imm : (BitVec 16)) : SailM Unit := do
  let w__5 ← (( do
    if ((← do
         if (((! (HaveEL EL2)) : Bool) : Bool)
         then (pure true)
         else
           (do
             let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__0.EL == EL0) : Bool))))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__2.EL == EL1) : Bool)))) : Bool)
        then
          (do
            let w__3 ← (( do (EL2Enabled ()) ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false)) ) : SailM Bool )
  if (w__5 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let hvc_enable ← (( do
    if ((HaveEL EL3) : Bool)
    then
      (do
        let w__6 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_SCR_EL3_Type_HCE w__6))))
    else
      (do
        let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((Complement.complement (_get_HCR_EL2_Type_HCD w__7))))) ) : SailM (BitVec 1) )
  if ((hvc_enable == 0#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      (AArch64_CallHypervisor imm))


def execute_aarch64_instrs_system_exceptions_runtime_smc (imm : (BitVec 16)) : SailM Unit := do
  (AArch64_CheckForSMCUndefOrTrap imm)
  (AArch64_CallSecureMonitor imm)


def execute_aarch64_instrs_system_exceptions_runtime_svc (imm : (BitVec 16)) : SailM Unit := do
  (AArch64_CheckForSVCTrap imm)
  (AArch64_CallSupervisor imm)


/-- Type quantifiers: VL : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ (is_VL VL) -/
def execute_aarch64_instrs_system_tme_tstart (VL : Nat) (t : Nat) : SailM Unit := do
  let w__0 ← (( do (IsTMEEnabled ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let IsEL1Regime ← (( do (undefined_bool_at (← occLabel 5021) ()) ) : SailM Bool )
  let tme ← (( do (undefined_bitvector_at (← occLabel 5022) 1) ) : SailM (BitVec 1) )
  let tmt ← (( do (undefined_bitvector_at (← occLabel 5023) 1) ) : SailM (BitVec 1) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let questionMark := w__1.EL
  let (tme, tmt) ← (( do
    if ((questionMark == EL0) : Bool)
    then
      (do
        let w__2 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
        let IsEL1Regime : Bool := (w__2 == EL1)
        if (IsEL1Regime : Bool)
        then
          (do
            let w__3 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            let tme := ((_get_SCTLR_EL1_Type_TME0 w__3) : (BitVec 1))
            let w__4 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            let tmt := ((_get_SCTLR_EL1_Type_TMT0 w__4) : (BitVec 1))
            (pure ((tme, tmt))))
        else
          (do
            let w__5 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
            let tme := ((_get_SCTLR_EL2_Type_TME0 w__5) : (BitVec 1))
            let w__6 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
            let tmt := ((_get_SCTLR_EL2_Type_TMT0 w__6) : (BitVec 1))
            (pure ((tme, tmt)))))
    else
      (do
        if ((questionMark == EL1) : Bool)
        then
          (do
            let w__7 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            let tme := ((_get_SCTLR_EL1_Type_TME w__7) : (BitVec 1))
            let w__8 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            let tmt := ((_get_SCTLR_EL1_Type_TMT w__8) : (BitVec 1))
            (pure ((tme, tmt))))
        else
          (do
            if ((questionMark == EL2) : Bool)
            then
              (do
                let w__9 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
                let tme := ((_get_SCTLR_EL2_Type_TME w__9) : (BitVec 1))
                let w__10 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
                let tmt := ((_get_SCTLR_EL2_Type_TMT w__10) : (BitVec 1))
                (pure ((tme, tmt))))
            else
              (do
                if ((questionMark == EL3) : Bool)
                then
                  (do
                    let w__11 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
                    let tme := ((_get_SCTLR_EL3_Type_TME w__11) : (BitVec 1))
                    let w__12 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
                    let tmt := ((_get_SCTLR_EL3_Type_TMT w__12) : (BitVec 1))
                    (pure ((tme, tmt))))
                else
                  (do
                    (Unreachable ())
                    (pure ((tme, tmt))))))) ) : SailM ((BitVec 1) × (BitVec 1)) )
  let enable : Bool := (tme == 1#1)
  let trivial : Bool := (tmt == 1#1)
  if ((! enable) : Bool)
  then
    (do
      (TransactionStartTrap t))
  else
    (do
      if (trivial : Bool)
      then
        (do
          let w__13 ← (( do readReg TSTATE ) : SailM TMState )
          let w__14 ← (( do (NextInstrAddr 64) ) : SailM (BitVec 64) )
          writeReg TSTATE { w__13 with nPC := w__14 }
          let w__15 ← (( do readReg TSTATE ) : SailM TMState )
          writeReg TSTATE { w__15 with Rt := t }
          (FailTransaction TMFailure_TRIVIAL false))
      else
        (do
          let w__18 ← (( do
            if ((← do
                 (HaveSME ())) : Bool)
            then
              (do
                let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
                (pure (((w__17.SM == 1#1) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__18 : Bool)
          then
            (do
              (FailTransaction TMFailure_ERR false))
          else
            (do
              let w__19 ← (( do readReg TSTATE ) : SailM TMState )
              if ((w__19.depth == 255) : Bool)
              then
                (do
                  (FailTransaction TMFailure_NEST false))
              else
                (do
                  let w__20 ← (( do readReg TSTATE ) : SailM TMState )
                  if ((w__20.depth == 0) : Bool)
                  then
                    (do
                      let w__21 ← (( do readReg TSTATE ) : SailM TMState )
                      let w__22 ← (( do (NextInstrAddr 64) ) : SailM (BitVec 64) )
                      writeReg TSTATE { w__21 with nPC := w__22 }
                      let w__23 ← (( do readReg TSTATE ) : SailM TMState )
                      writeReg TSTATE { w__23 with Rt := t }
                      let _ : Unit := (ClearExclusiveLocal (ProcessorID ()))
                      (TakeTransactionCheckpoint VL (Int.ediv VL 8))
                      (pure ((StartTrackingTransactionalReadsWrites ()))))
                  else (pure (()))))))
  let w__24 ← (( do readReg TSTATE ) : SailM TMState )
  let w__25 ← (( do readReg TSTATE ) : SailM TMState )
  writeReg TSTATE { w__24 with depth := (w__25.depth +i 1) }
  (X_set t 64 (Zeros (n := 64)))


end ArmFull.Functions
