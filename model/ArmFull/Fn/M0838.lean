import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0021
import ArmFull.Fn.M0063
import ArmFull.Fn.M0124
import ArmFull.Fn.M0150
import ArmFull.Fn.M0159
import ArmFull.Fn.M0169
import ArmFull.Fn.M0175
import ArmFull.Fn.M0578

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

def decode_aarch32_instrs_EOR_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:3115.29-3115.30"
      let carry ← (( do (undefined_bitvector_at (← occLabel 3014) 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3015) 32) ) : SailM (BitVec 32) )
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (A32ExpandImm_C imm12 w__1.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
      let (tup__0, tup__1) := (w__2 : ((BitVec 32) × (BitVec 1)))
      let imm32 : (BitVec 32) := tup__0
      let carry : (BitVec 1) := tup__1
      (execute_aarch32_instrs_EOR_i_Op_A_txt carry (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_EOR_i_T1enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let carry ← (( do (undefined_bitvector_at (← occLabel 3016) 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3017) 32) ) : SailM (BitVec 32) )
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then sailThrow ((Error_See "TEQ (immediate)"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (T32ExpandImm_C ((i +++ imm3) +++ imm8) w__1.C) ) : SailM
        ((BitVec 32) × (BitVec 1)) )
      let (tup__0, tup__1) := (w__2 : ((BitVec 32) × (BitVec 1)))
      let imm32 : (BitVec 32) := tup__0
      let carry : (BitVec 1) := tup__1
      if ((((d == 15) && (! setflags)) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_EOR_i_Op_A_txt carry (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_EOR_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:3199.29-3199.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 3020) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3021) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do (DecodeImmShift stype imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_EOR_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_EOR_r_T1enc_A_txt (Rm : (BitVec 3)) (Rdn : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3022) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3023) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rdn)
      let n : Int := (BitVec.toNat Rdn)
      let m : Int := (BitVec.toNat Rm)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      let setflags : Bool := (! w__1)
      let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
      let shift_t : SRType := tup__0
      let shift_n : Int := (Sail.Int.toNatChecked (tup__1))
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_EOR_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_EOR_r_T2enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3024) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3025) ()) ) : SailM SRType )
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then sailThrow ((Error_See "TEQ (register)"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do (DecodeImmShift stype (imm3 +++ imm2)) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if (((((d == 15) && (! setflags)) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_EOR_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_MOV_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:7338.29-7338.30"
      let carry ← (( do (undefined_bitvector_at (← occLabel 3110) 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3111) 32) ) : SailM (BitVec 32) )
      let d : Int := (BitVec.toNat Rd)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (A32ExpandImm_C imm12 w__1.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
      let (tup__0, tup__1) := (w__2 : ((BitVec 32) × (BitVec 1)))
      let imm32 : (BitVec 32) := tup__0
      let carry : (BitVec 1) := tup__1
      (execute_aarch32_instrs_MOV_i_Op_A_txt carry (Sail.Int.toNatChecked (d)) imm32 setflags))
  else (pure (()))


def decode_aarch32_instrs_MOV_i_A2enc_A_txt (cond : (BitVec 4)) (imm4 : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:7366.29-7366.30"
      let carry ← (( do (undefined_bitvector_at (← occLabel 3112) 1) ) : SailM (BitVec 1) )
      let d : Int := (BitVec.toNat Rd)
      let setflags : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4 +++ imm12) 32)
      if ((d == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let carry := carry
      (execute_aarch32_instrs_MOV_i_Op_A_txt carry (Sail.Int.toNatChecked (d)) imm32 setflags))
  else (pure (()))


def decode_aarch32_instrs_MOV_i_T1enc_A_txt (Rd : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      let setflags : Bool := (! w__1)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      let carry : (BitVec 1) := w__2.C
      (execute_aarch32_instrs_MOV_i_Op_A_txt carry (Sail.Int.toNatChecked (d)) imm32 setflags))
  else (pure (()))


def decode_aarch32_instrs_MOV_i_T2enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let carry ← (( do (undefined_bitvector_at (← occLabel 3113) 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3114) 32) ) : SailM (BitVec 32) )
      let d : Int := (BitVec.toNat Rd)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (T32ExpandImm_C ((i +++ imm3) +++ imm8) w__1.C) ) : SailM
        ((BitVec 32) × (BitVec 1)) )
      let (tup__0, tup__1) := (w__2 : ((BitVec 32) × (BitVec 1)))
      let imm32 : (BitVec 32) := tup__0
      let carry : (BitVec 1) := tup__1
      if ((d == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let imm32 := imm32
      let carry := carry
      (execute_aarch32_instrs_MOV_i_Op_A_txt carry (Sail.Int.toNatChecked (d)) imm32 setflags))
  else (pure (()))


def decode_aarch32_instrs_MOV_i_T3enc_A_txt (i : (BitVec 1)) (imm4 : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let carry ← (( do (undefined_bitvector_at (← occLabel 3115) 1) ) : SailM (BitVec 1) )
      let d : Int := (BitVec.toNat Rd)
      let setflags : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (((imm4 +++ i) +++ imm3) +++ imm8) 32)
      if ((d == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let carry := carry
      (execute_aarch32_instrs_MOV_i_Op_A_txt carry (Sail.Int.toNatChecked (d)) imm32 setflags))
  else (pure (()))


def decode_aarch32_instrs_MOV_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:7495.29-7495.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 3118) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3119) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do (DecodeImmShift stype imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_MOV_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_MOV_r_T1enc_A_txt (D : (BitVec 1)) (Rm : (BitVec 4)) (Rd : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3120) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3121) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat (D +++ Rd))
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := false
      let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
      let shift_t : SRType := tup__0
      let shift_n : Int := (Sail.Int.toNatChecked (tup__1))
      let shift_n : Int := shift_n
      let w__4 ← (( do
        if ((← do
             if (((d == 15) : Bool) : Bool)
             then
               (do
                 (InITBlock ()))
             else (pure false)) : Bool)
        then
          (do
            let w__3 ← (( do (LastInITBlock ()) ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let shift_t := shift_t
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_MOV_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_MOV_r_T2enc_A_txt (Rm : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3122) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3123) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := true
      let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
      let shift_t : SRType := tup__0
      let shift_n : Int := (Sail.Int.toNatChecked (tup__1))
      let shift_n : Int := shift_n
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let shift_t := shift_t
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_MOV_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_MOV_r_T3enc_A_txt (S : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3124) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3125) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do (DecodeImmShift stype (imm3 +++ imm2)) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if (((d == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let shift_t := shift_t
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_MOV_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_MVN_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:8009.29-8009.30"
      let carry ← (( do (undefined_bitvector_at (← occLabel 3128) 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3129) 32) ) : SailM (BitVec 32) )
      let d : Int := (BitVec.toNat Rd)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (A32ExpandImm_C imm12 w__1.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
      let (tup__0, tup__1) := (w__2 : ((BitVec 32) × (BitVec 1)))
      let imm32 : (BitVec 32) := tup__0
      let carry : (BitVec 1) := tup__1
      (execute_aarch32_instrs_MVN_i_Op_A_txt carry (Sail.Int.toNatChecked (d)) imm32 setflags))
  else (pure (()))


def decode_aarch32_instrs_MVN_i_T1enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let carry ← (( do (undefined_bitvector_at (← occLabel 3130) 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3131) 32) ) : SailM (BitVec 32) )
      let d : Int := (BitVec.toNat Rd)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (T32ExpandImm_C ((i +++ imm3) +++ imm8) w__1.C) ) : SailM
        ((BitVec 32) × (BitVec 1)) )
      let (tup__0, tup__1) := (w__2 : ((BitVec 32) × (BitVec 1)))
      let imm32 : (BitVec 32) := tup__0
      let carry : (BitVec 1) := tup__1
      if ((d == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let imm32 := imm32
      let carry := carry
      (execute_aarch32_instrs_MVN_i_Op_A_txt carry (Sail.Int.toNatChecked (d)) imm32 setflags))
  else (pure (()))


def decode_aarch32_instrs_MVN_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:8092.29-8092.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 3134) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3135) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do (DecodeImmShift stype imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_MVN_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_MVN_r_T1enc_A_txt (Rm : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3136) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3137) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      let setflags : Bool := (! w__1)
      let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
      let shift_t : SRType := tup__0
      let shift_n : Int := (Sail.Int.toNatChecked (tup__1))
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_MVN_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_MVN_r_T2enc_A_txt (S : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3138) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3139) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do (DecodeImmShift stype (imm3 +++ imm2)) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if (((d == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let shift_t := shift_t
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_MVN_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_ORR_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:8420.29-8420.30"
      let carry ← (( do (undefined_bitvector_at (← occLabel 3148) 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3149) 32) ) : SailM (BitVec 32) )
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (A32ExpandImm_C imm12 w__1.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
      let (tup__0, tup__1) := (w__2 : ((BitVec 32) × (BitVec 1)))
      let imm32 : (BitVec 32) := tup__0
      let carry : (BitVec 1) := tup__1
      (execute_aarch32_instrs_ORR_i_Op_A_txt carry (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_ORR_i_T1enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let carry ← (( do (undefined_bitvector_at (← occLabel 3150) 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3151) 32) ) : SailM (BitVec 32) )
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "MOV (immediate)"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (T32ExpandImm_C ((i +++ imm3) +++ imm8) w__1.C) ) : SailM
        ((BitVec 32) × (BitVec 1)) )
      let (tup__0, tup__1) := (w__2 : ((BitVec 32) × (BitVec 1)))
      let imm32 : (BitVec 32) := tup__0
      let carry : (BitVec 1) := tup__1
      if ((d == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_ORR_i_Op_A_txt carry (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_ORR_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:8504.29-8504.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 3154) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3155) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do (DecodeImmShift stype imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_ORR_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_ORR_r_T1enc_A_txt (Rm : (BitVec 3)) (Rdn : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3156) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3157) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rdn)
      let n : Int := (BitVec.toNat Rdn)
      let m : Int := (BitVec.toNat Rm)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      let setflags : Bool := (! w__1)
      let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
      let shift_t : SRType := tup__0
      let shift_n : Int := (Sail.Int.toNatChecked (tup__1))
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_ORR_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_ORR_r_T2enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3158) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3159) ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do (DecodeImmShift stype (imm3 +++ imm2)) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if (((d == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_ORR_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_RSB_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:10266.29-10266.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      (execute_aarch32_instrs_RSB_i_Op_A_txt (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_RSB_i_T1enc_A_txt (Rn : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      let setflags : Bool := (! w__1)
      let imm32 : (BitVec 32) := (Zeros (n := 32))
      (execute_aarch32_instrs_RSB_i_Op_A_txt (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_RSB_i_T2enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (T32ExpandImm ((i +++ imm3) +++ imm8)) ) : SailM (BitVec 32) )
      if (((d == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_RSB_i_Op_A_txt (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_RSB_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:10361.29-10361.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 3192) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3193) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do (DecodeImmShift stype imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_RSB_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_RSB_r_T1enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3194) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3195) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do (DecodeImmShift stype (imm3 +++ imm2)) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let shift_t := shift_t
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_RSB_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


end ArmFull.Functions
