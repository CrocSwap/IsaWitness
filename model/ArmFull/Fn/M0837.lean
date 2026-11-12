import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0021
import ArmFull.Fn.M0063
import ArmFull.Fn.M0124
import ArmFull.Fn.M0150
import ArmFull.Fn.M0159
import ArmFull.Fn.M0169
import ArmFull.Fn.M0175
import ArmFull.Fn.M0577
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

def decode_aarch32_instrs_ADC_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:68.29-68.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      (execute_aarch32_instrs_ADC_i_Op_A_txt (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_ADC_i_T1enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
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
      (execute_aarch32_instrs_ADC_i_Op_A_txt (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_ADC_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:143.29-143.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 2912) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 2913) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do (DecodeImmShift stype imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_ADC_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_ADC_r_T1enc_A_txt (Rm : (BitVec 3)) (Rdn : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 2914) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 2915) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rdn)
      let n : Int := (BitVec.toNat Rdn)
      let m : Int := (BitVec.toNat Rm)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      let setflags : Bool := (! w__1)
      let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
      let shift_t : SRType := tup__0
      let shift_n : Int := (Sail.Int.toNatChecked (tup__1))
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_ADC_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_ADC_r_T2enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 2916) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 2917) ()) ) : SailM SRType )
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
      (execute_aarch32_instrs_ADC_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_ADD_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:306.29-306.30"
      if (((Rn == 0b1111#4) && (S == 0#1)) : Bool)
      then sailThrow ((Error_See "ADR"))
      else (pure (()))
      if ((Rn == 0b1101#4) : Bool)
      then sailThrow ((Error_See "ADD (SP plus immediate)"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      (execute_aarch32_instrs_ADD_i_OpA_A_txt (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_ADD_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:481.29-481.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 2926) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 2927) ()) ) : SailM SRType )
      if ((Rn == 0b1101#4) : Bool)
      then sailThrow ((Error_See "ADD (SP plus register)"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do (DecodeImmShift stype imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_ADD_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_ADD_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 2928) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 2929) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      let setflags : Bool := (! w__1)
      let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
      let shift_t : SRType := tup__0
      let shift_n : Int := (Sail.Int.toNatChecked (tup__1))
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_ADD_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_ADD_r_T2enc_A_txt (DN : (BitVec 1)) (Rm : (BitVec 4)) (Rdn : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 2930) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 2931) ()) ) : SailM SRType )
      if ((((DN +++ Rdn) == 0b1101#4) || (Rm == 0b1101#4)) : Bool)
      then sailThrow ((Error_See "ADD (SP plus register)"))
      else (pure (()))
      let d : Int := (BitVec.toNat (DN +++ Rdn))
      let n : Int := d
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := false
      let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
      let shift_t : SRType := tup__0
      let shift_n : Int := (Sail.Int.toNatChecked (tup__1))
      let shift_n : Int := shift_n
      if (((n == 15) && (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
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
      (execute_aarch32_instrs_ADD_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_ADD_r_T3enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 2932) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 2933) ()) ) : SailM SRType )
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then sailThrow ((Error_See "CMN (register)"))
      else (pure (()))
      if ((Rn == 0b1101#4) : Bool)
      then sailThrow ((Error_See "ADD (SP plus register)"))
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
      (execute_aarch32_instrs_ADD_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_ADD_SP_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:685.29-685.30"
      let d : Int := (BitVec.toNat Rd)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      (execute_aarch32_instrs_ADD_SP_i_Op_A_txt (Sail.Int.toNatChecked (d)) imm32 setflags))
  else (pure (()))


def decode_aarch32_instrs_ADD_SP_i_T1enc_A_txt (Rd : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let setflags : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      (execute_aarch32_instrs_ADD_SP_i_Op_A_txt (Sail.Int.toNatChecked (d)) imm32 setflags))
  else (pure (()))


def decode_aarch32_instrs_ADD_SP_i_T2enc_A_txt (imm7 : (BitVec 7)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Nat := 13
      let setflags : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm7 +++ 0b00#2) 32)
      (execute_aarch32_instrs_ADD_SP_i_Op_A_txt d imm32 setflags))
  else (pure (()))


def decode_aarch32_instrs_ADD_SP_i_T3enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then sailThrow ((Error_See "CMN (immediate)"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (T32ExpandImm ((i +++ imm3) +++ imm8)) ) : SailM (BitVec 32) )
      if (((d == 15) && (! setflags)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_ADD_SP_i_Op_A_txt (Sail.Int.toNatChecked (d)) imm32 setflags))
  else (pure (()))


def decode_aarch32_instrs_ADD_SP_i_T4enc_A_txt (i : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let setflags : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend ((i +++ imm3) +++ imm8) 32)
      if ((d == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_ADD_SP_i_Op_A_txt (Sail.Int.toNatChecked (d)) imm32 setflags))
  else (pure (()))


def decode_aarch32_instrs_ADD_SP_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:820.29-820.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 2940) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 2941) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do (DecodeImmShift stype imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_ADD_SP_r_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_ADD_SP_r_T1enc_A_txt (DM : (BitVec 1)) (Rdm : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 2942) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 2943) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat (DM +++ Rdm))
      let m : Int := (BitVec.toNat (DM +++ Rdm))
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
      (execute_aarch32_instrs_ADD_SP_r_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_ADD_SP_r_T2enc_A_txt (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 2944) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 2945) ()) ) : SailM SRType )
      if ((Rm == 0b1101#4) : Bool)
      then sailThrow ((Error_See "encoding T1"))
      else (pure (()))
      let d : Nat := 13
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := false
      let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
      let shift_t : SRType := tup__0
      let shift_n : Int := (Sail.Int.toNatChecked (tup__1))
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_ADD_SP_r_Op_A_txt d (Sail.Int.toNatChecked (m)) setflags shift_n
        shift_t))
  else (pure (()))


def decode_aarch32_instrs_ADD_SP_r_T3enc_A_txt (S : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 2946) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 2947) ()) ) : SailM SRType )
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then sailThrow ((Error_See "CMN (register)"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do (DecodeImmShift stype (imm3 +++ imm2)) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if ((((d == 15) && (! setflags)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_ADD_SP_r_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_AND_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:1083.29-1083.30"
      let carry ← (( do (undefined_bitvector_at (← occLabel 2948) 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 2949) 32) ) : SailM (BitVec 32) )
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (A32ExpandImm_C imm12 w__1.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
      let (tup__0, tup__1) := (w__2 : ((BitVec 32) × (BitVec 1)))
      let imm32 : (BitVec 32) := tup__0
      let carry : (BitVec 1) := tup__1
      (execute_aarch32_instrs_AND_i_Op_A_txt carry (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_AND_i_T1enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let carry ← (( do (undefined_bitvector_at (← occLabel 2950) 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 2951) 32) ) : SailM (BitVec 32) )
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then sailThrow ((Error_See "TST (immediate)"))
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
      (execute_aarch32_instrs_AND_i_Op_A_txt carry (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_AND_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:1167.29-1167.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 2954) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 2955) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do (DecodeImmShift stype imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_AND_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_AND_r_T1enc_A_txt (Rm : (BitVec 3)) (Rdn : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 2956) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 2957) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rdn)
      let n : Int := (BitVec.toNat Rdn)
      let m : Int := (BitVec.toNat Rm)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      let setflags : Bool := (! w__1)
      let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
      let shift_t : SRType := tup__0
      let shift_n : Int := (Sail.Int.toNatChecked (tup__1))
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_AND_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_AND_r_T2enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 2958) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 2959) ()) ) : SailM SRType )
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then sailThrow ((Error_See "TST (register)"))
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
      (execute_aarch32_instrs_AND_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_BIC_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:1687.29-1687.30"
      let carry ← (( do (undefined_bitvector_at (← occLabel 2967) 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 2968) 32) ) : SailM (BitVec 32) )
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (A32ExpandImm_C imm12 w__1.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
      let (tup__0, tup__1) := (w__2 : ((BitVec 32) × (BitVec 1)))
      let imm32 : (BitVec 32) := tup__0
      let carry : (BitVec 1) := tup__1
      (execute_aarch32_instrs_BIC_i_Op_A_txt carry (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_BIC_i_T1enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let carry ← (( do (undefined_bitvector_at (← occLabel 2969) 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 2970) 32) ) : SailM (BitVec 32) )
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (T32ExpandImm_C ((i +++ imm3) +++ imm8) w__1.C) ) : SailM
        ((BitVec 32) × (BitVec 1)) )
      let (tup__0, tup__1) := (w__2 : ((BitVec 32) × (BitVec 1)))
      let imm32 : (BitVec 32) := tup__0
      let carry : (BitVec 1) := tup__1
      if (((d == 15) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let imm32 := imm32
      let carry := carry
      (execute_aarch32_instrs_BIC_i_Op_A_txt carry (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_BIC_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:1770.29-1770.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 2973) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 2974) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do (DecodeImmShift stype imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_BIC_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_BIC_r_T1enc_A_txt (Rm : (BitVec 3)) (Rdn : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 2975) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 2976) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rdn)
      let n : Int := (BitVec.toNat Rdn)
      let m : Int := (BitVec.toNat Rm)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      let setflags : Bool := (! w__1)
      let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
      let shift_t : SRType := tup__0
      let shift_n : Int := (Sail.Int.toNatChecked (tup__1))
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_BIC_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_BIC_r_T2enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 2977) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 2978) ()) ) : SailM SRType )
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
      (execute_aarch32_instrs_BIC_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


end ArmFull.Functions
