module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0018
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0063
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0124
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0148
public import ArmFull.Fn.M0151
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0172
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0183
public import ArmFull.Fn.M0187
public import ArmFull.Fn.M0251
public import ArmFull.Fn.M0252
public import ArmFull.Fn.M0253
public import ArmFull.Fn.M0256
public import ArmFull.Fn.M0258
public import ArmFull.Fn.M0601
public import ArmFull.Fn.M0602 set_option backward.proofsInPublic true @[expose] public section

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

def decode_aarch32_instrs_RSC_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:10500.29-10500.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      (execute_aarch32_instrs_RSC_i_Op_A_txt (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_RSC_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:10548.29-10548.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 3202) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3203) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do (DecodeImmShift stype imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_RSC_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_SBC_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:10895.29-10895.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      (execute_aarch32_instrs_SBC_i_Op_A_txt (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_SBC_i_T1enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
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
      (execute_aarch32_instrs_SBC_i_Op_A_txt (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_SBC_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:10970.29-10970.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 3210) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3211) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do (DecodeImmShift stype imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_SBC_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_SBC_r_T1enc_A_txt (Rm : (BitVec 3)) (Rdn : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3212) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3213) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rdn)
      let n : Int := (BitVec.toNat Rdn)
      let m : Int := (BitVec.toNat Rm)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      let setflags : Bool := (! w__1)
      let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
      let shift_t : SRType := tup__0
      let shift_n : Int := (Sail.Int.toNatChecked (tup__1))
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_SBC_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_SBC_r_T2enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3214) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3215) ()) ) : SailM SRType )
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
      (execute_aarch32_instrs_SBC_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_SUB_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:15507.29-15507.30"
      if (((Rn == 0b1111#4) && (S == 0#1)) : Bool)
      then sailThrow ((Error_See "ADR"))
      else (pure (()))
      if ((Rn == 0b1101#4) : Bool)
      then sailThrow ((Error_See "SUB (SP minus immediate)"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      (execute_aarch32_instrs_SUB_i_Op_A_txt (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_SUB_i_T1enc_A_txt (imm3 : (BitVec 3)) (Rn : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      let setflags : Bool := (! w__1)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm3 32)
      (execute_aarch32_instrs_SUB_i_Op_A_txt (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_SUB_i_T2enc_A_txt (Rdn : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rdn)
      let n : Int := (BitVec.toNat Rdn)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      let setflags : Bool := (! w__1)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      (execute_aarch32_instrs_SUB_i_Op_A_txt (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_SUB_i_T3enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then sailThrow ((Error_See "CMP (immediate)"))
      else (pure (()))
      if ((Rn == 0b1101#4) : Bool)
      then sailThrow ((Error_See "SUB (SP minus immediate)"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (T32ExpandImm ((i +++ imm3) +++ imm8)) ) : SailM (BitVec 32) )
      if ((((d == 15) && (! setflags)) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SUB_i_Op_A_txt (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_SUB_i_T4enc_A_txt (i : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "ADR"))
      else (pure (()))
      if ((Rn == 0b1101#4) : Bool)
      then sailThrow ((Error_See "SUB (SP minus immediate)"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let setflags : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend ((i +++ imm3) +++ imm8) 32)
      if ((d == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SUB_i_Op_A_txt (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_SUB_i_T5enc_A_txt (Rn : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Rn == 0b1110#4) && (IsZero imm8)) : Bool)
      then sailThrow ((Error_See "ERET"))
      else (pure (()))
      let d : Nat := 15
      let n : Int := (BitVec.toNat Rn)
      let setflags : Bool := true
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      if ((n != 14) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
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
      (execute_aarch32_instrs_SUB_i_Op_A_txt d imm32 (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_SUB_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:15700.29-15700.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 3280) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3281) ()) ) : SailM SRType )
      if ((Rn == 0b1101#4) : Bool)
      then sailThrow ((Error_See "SUB (SP minus register)"))
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
      (execute_aarch32_instrs_SUB_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_SUB_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3282) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3283) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      let setflags : Bool := (! w__1)
      let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
      let shift_t : SRType := tup__0
      let shift_n : Int := (Sail.Int.toNatChecked (tup__1))
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_SUB_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_SUB_r_T2enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3284) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3285) ()) ) : SailM SRType )
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then sailThrow ((Error_See "CMP (register)"))
      else (pure (()))
      if ((Rn == 0b1101#4) : Bool)
      then sailThrow ((Error_See "SUB (SP minus register)"))
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
      (execute_aarch32_instrs_SUB_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_SUB_SP_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:15870.29-15870.30"
      let d : Int := (BitVec.toNat Rd)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      (execute_aarch32_instrs_SUB_SP_i_Op_A_txt (Sail.Int.toNatChecked (d)) imm32 setflags))
  else (pure (()))


def decode_aarch32_instrs_SUB_SP_i_T1enc_A_txt (imm7 : (BitVec 7)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Nat := 13
      let setflags : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm7 +++ 0b00#2) 32)
      (execute_aarch32_instrs_SUB_SP_i_Op_A_txt d imm32 setflags))
  else (pure (()))


def decode_aarch32_instrs_SUB_SP_i_T2enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then sailThrow ((Error_See "CMP (immediate)"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (T32ExpandImm ((i +++ imm3) +++ imm8)) ) : SailM (BitVec 32) )
      if (((d == 15) && (! setflags)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SUB_SP_i_Op_A_txt (Sail.Int.toNatChecked (d)) imm32 setflags))
  else (pure (()))


def decode_aarch32_instrs_SUB_SP_i_T3enc_A_txt (i : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
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
      (execute_aarch32_instrs_SUB_SP_i_Op_A_txt (Sail.Int.toNatChecked (d)) imm32 setflags))
  else (pure (()))


def decode_aarch32_instrs_SUB_SP_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:15986.29-15986.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 3292) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3293) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let w__1 ← (( do (DecodeImmShift stype imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_SUB_SP_r_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_SUB_SP_r_T1enc_A_txt (S : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3294) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3295) ()) ) : SailM SRType )
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then sailThrow ((Error_See "CMP (register)"))
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
      (execute_aarch32_instrs_SUB_SP_r_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) setflags shift_n shift_t))
  else (pure (()))


def execute_aarch32_instrs_SVC_Op_A_txt (imm32 : (BitVec 32)) : SailM Unit := do
  (AArch32_CheckForSVCTrap (Sail.BitVec.extractLsb imm32 15 0))
  (AArch32_CallSupervisor (Sail.BitVec.extractLsb imm32 15 0))


def execute_aarch32_instrs_HVC_Op_AS_txt (imm16 : (BitVec 16)) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__0.EL == EL0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL3) : Bool))))) : Bool)
    then (pure true)
    else
      (do
        let w__3 ← (( do (EL2Enabled ()) ) : SailM Bool )
        (pure (((! w__3) : Bool)))) ) : SailM Bool )
  if (w__4 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let hvc_enable ← (( do (undefined_bitvector_at (← occLabel 3776) 1) ) : SailM (BitVec 1) )
  let w__5 ← (( do (HaveEL EL3) ) : SailM Bool )
  let hvc_enable ← (( do
    if (w__5 : Bool)
    then
      (do
        let w__10 ← (( do
          if ((← do
               if ((← do
                    (ELUsingAArch32 EL3)) : Bool)
               then
                 (do
                   let w__7 ← (( do readReg SCR ) : SailM (BitVec 32) )
                   (pure ((((_get_SCR_Type_HCE w__7) == 0#1) : Bool))))
               else (pure false)) : Bool)
          then
            (do
              let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__9.EL == EL2) : Bool))))
          else (pure false) ) : SailM Bool )
        if (w__10 : Bool)
        then sailThrow ((Error_Unpredictable ()))
        else
          (do
            let w__11 ← (( do (SCR_GEN_read ()) ) : SailM (BitVec 64) )
            let hvc_enable := ((_get_SCRType_HCE w__11) : (BitVec 1))
            (pure (hvc_enable))))
    else
      (do
        let w__12 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
        if (w__12 : Bool)
        then
          (do
            let w__13 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
            (pure ((Complement.complement (_get_HCR_Type_HCD w__13)))))
        else
          (do
            let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((Complement.complement (_get_HCR_EL2_Type_HCD w__14)))))) ) : SailM (BitVec 1) )
  if ((hvc_enable == 0#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      (AArch32_CallHypervisor imm16))


def decode_aarch32_instrs_MRS_br_A1enc_AS_txt (cond : (BitVec 4)) (R : (BitVec 1)) (M1 : (BitVec 4)) (Rd : (BitVec 4)) (M : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:41246.29-41246.30"
      let d : Int := (BitVec.toNat Rd)
      let read_spsr : Bool := (R == 1#1)
      if ((d == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let SYSm : (BitVec 5) := (M +++ M1)
      (execute_aarch32_instrs_MRS_br_Op_AS_txt SYSm (Sail.Int.toNatChecked (d)) read_spsr))
  else (pure (()))


def decode_aarch32_instrs_MRS_br_T1enc_AS_txt (R : (BitVec 1)) (M1 : (BitVec 4)) (Rd : (BitVec 4)) (M : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let read_spsr : Bool := (R == 1#1)
      if ((d == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let SYSm : (BitVec 5) := (M +++ M1)
      (execute_aarch32_instrs_MRS_br_Op_AS_txt SYSm (Sail.Int.toNatChecked (d)) read_spsr))
  else (pure (()))


def decode_aarch32_instrs_MSR_br_A1enc_AS_txt (cond : (BitVec 4)) (R : (BitVec 1)) (M1 : (BitVec 4)) (M : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:41390.29-41390.30"
      let n : Int := (BitVec.toNat Rn)
      let write_spsr : Bool := (R == 1#1)
      if ((n == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let SYSm : (BitVec 5) := (M +++ M1)
      (execute_aarch32_instrs_MSR_br_Op_AS_txt SYSm (Sail.Int.toNatChecked (n)) write_spsr))
  else (pure (()))


def decode_aarch32_instrs_MSR_br_T1enc_AS_txt (R : (BitVec 1)) (Rn : (BitVec 4)) (M1 : (BitVec 4)) (M : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let n : Int := (BitVec.toNat Rn)
      let write_spsr : Bool := (R == 1#1)
      if ((n == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let SYSm : (BitVec 5) := (M +++ M1)
      (execute_aarch32_instrs_MSR_br_Op_AS_txt SYSm (Sail.Int.toNatChecked (n)) write_spsr))
  else (pure (()))


def execute_aarch32_instrs_SMC_Op_AS_txt (_ : Unit) : SailM Unit := do
  let c ← (( do (undefined_Constraint (← occLabel 3790) ()) ) : SailM Constraint )
  (AArch32_CheckForSMCUndefOrTrap ())
  let w__0 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
      if (((_get_SCR_EL3_Type_SMD w__1) == 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (())))
  else
    (do
      let w__2 ← (( do readReg SCR ) : SailM (BitVec 32) )
      if (((_get_SCR_Type_SCD w__2) == 1#1) : Bool)
      then
        (do
          let w__3 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
          if ((BEq.beq w__3 SS_Secure) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_SMD) ) : SailM Constraint )
              ArmFull.assert ((BEq.beq c Constraint_NOP) || (BEq.beq c Constraint_UNDEF)) "sail-inputs/14-instrs32.sail:41695.66-41695.67"
              if ((BEq.beq c Constraint_NOP) : Bool)
              then
                (do
                  (EndOfInstruction ()))
              else (pure (())))
          else (pure (()))
          sailThrow ((Error_Undefined ())))
      else (pure (())))
  let w__4 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
  if ((! w__4) : Bool)
  then
    (do
      (AArch64_CallSecureMonitor (Zeros (n := 16))))
  else
    (do
      (AArch32_TakeSMCException ()))


def execute_aarch64_instrs_system_register_cpsr (field : PSTATEField) (operand : (BitVec 4)) : SailM Unit := do
  match field with
  | .PSTATEField_SSBS =>
    (do
      let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__0 with SSBS := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand 0)])) })
  | .PSTATEField_SP =>
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with SP := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand 0)])) })
  | .PSTATEField_DAIFSet =>
    (do
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with D := (w__3.D ||| (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
              operand 3)]))) }
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with A := (w__5.A ||| (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
              operand 2)]))) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with I := (w__7.I ||| (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
              operand 1)]))) }
      let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__8 with F := (w__9.F ||| (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
              operand 0)]))) })
  | .PSTATEField_DAIFClr =>
    (do
      let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__10 with D := (w__11.D &&& (Complement.complement
            (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand 3)])))) }
      let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__12 with A := (w__13.A &&& (Complement.complement
            (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand 2)])))) }
      let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__14 with I := (w__15.I &&& (Complement.complement
            (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand 1)])))) }
      let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__16 with F := (w__17.F &&& (Complement.complement
            (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand 0)])))) })
  | .PSTATEField_PAN =>
    (do
      let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__18 with PAN := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand 0)])) })
  | .PSTATEField_UAO =>
    (do
      let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__19 with UAO := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand 0)])) })
  | .PSTATEField_DIT =>
    (do
      let w__20 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__20 with DIT := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand 0)])) })
  | .PSTATEField_TCO =>
    (do
      let w__21 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__21 with TCO := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand 0)])) })
  | .PSTATEField_ALLINT =>
    (do
      let w__27 ← (( do
        (pure ((← do
              if ((← do
                   if ((← do
                        let w__22 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__22.EL == EL1) : Bool)))) : Bool)
                   then
                     (do
                       (IsHCRXEL2Enabled ()))
                   else (pure false)) : Bool)
              then
                (do
                  let w__25 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCRX_EL2_Type_TALLINT w__25) == 1#1) : Bool))))
              else (pure false)) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand 0)])) == 1#1) : Bool)))
        ) : SailM Bool )
      if (w__27 : Bool)
      then
        (do
          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
      else (pure (()))
      let w__28 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__28 with ALLINT := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
            operand 0)])) })
  | .PSTATEField_SVCRSM =>
    (do
      (CheckSMEAccess ())
      (SetPSTATE_SM (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand 0)]))))
  | .PSTATEField_SVCRZA =>
    (do
      (CheckSMEAccess ())
      (SetPSTATE_ZA (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand 0)]))))
  | .PSTATEField_SVCRSMZA =>
    (do
      (CheckSMEAccess ())
      (SetPSTATE_SM (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand 0)])))
      (SetPSTATE_ZA (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand 0)]))))
  | .PSTATEField_PM =>
    (do
      let w__29 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__29 with PM := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand 0)])) })


end ArmFull.Functions
