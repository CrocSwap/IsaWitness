import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0021
import ArmFull.Fn.M0086
import ArmFull.Fn.M0124
import ArmFull.Fn.M0144
import ArmFull.Fn.M0175
import ArmFull.Fn.M0202
import ArmFull.Fn.M0215
import ArmFull.Fn.M0222

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

def decode_aarch32_instrs_EOR_rr_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:3311.29-3311.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let s : Int := (BitVec.toNat Rs)
      let setflags : Bool := (S == 1#1)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if (((((d == 15) || (n == 15)) || (m == 15)) || (s == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_EOR_rr_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (s)) setflags
        shift_t))
  else (pure (()))


def decode_aarch32_instrs_LSL_i_T1enc_A_txt (imm5 : (BitVec 5)) (Rm : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3102) ()) ) : SailM Int )
      if ((imm5 == 0b00000#5) : Bool)
      then sailThrow ((Error_See "MOV (register)"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      let setflags : Bool := (! w__1)
      let (_, __tup_1) ← (( do (DecodeImmShift 0b00#2 imm5) ) : SailM (SRType × Int) )
      let shift_n : Int := __tup_1
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_LSL_i_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        setflags shift_n))
  else (pure (()))


def decode_aarch32_instrs_LSL_r_T1enc_A_txt (Rm : (BitVec 3)) (Rdn : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rdn)
      let n : Int := (BitVec.toNat Rdn)
      let m : Int := (BitVec.toNat Rm)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      let setflags : Bool := (! w__1)
      (execute_aarch32_instrs_LSL_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_LSL_r_T2enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LSL_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_LSR_i_T1enc_A_txt (imm5 : (BitVec 5)) (Rm : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3107) ()) ) : SailM Int )
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      let setflags : Bool := (! w__1)
      let (_, __tup_1) ← (( do (DecodeImmShift 0b01#2 imm5) ) : SailM (SRType × Int) )
      let shift_n : Int := __tup_1
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_LSR_i_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        setflags shift_n))
  else (pure (()))


def decode_aarch32_instrs_LSR_r_T1enc_A_txt (Rm : (BitVec 3)) (Rdn : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rdn)
      let n : Int := (BitVec.toNat Rdn)
      let m : Int := (BitVec.toNat Rm)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      let setflags : Bool := (! w__1)
      (execute_aarch32_instrs_LSR_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_MLA_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (Ra : (BitVec 4)) (Rm : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:7194.29-7194.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let a : Int := (BitVec.toNat Ra)
      let setflags : Bool := (S == 1#1)
      if (((((d == 15) || (n == 15)) || (m == 15)) || (a == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_MLA_Op_A_txt (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_MLA_T1enc_A_txt (Rn : (BitVec 4)) (Ra : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Ra == 0b1111#4) : Bool)
      then sailThrow ((Error_See "MUL"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let a : Int := (BitVec.toNat Ra)
      let setflags : Bool := false
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_MLA_Op_A_txt (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_MLS_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Ra : (BitVec 4)) (Rm : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:7264.29-7264.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let a : Int := (BitVec.toNat Ra)
      if (((((d == 15) || (n == 15)) || (m == 15)) || (a == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_MLS_Op_A_txt (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_MLS_T1enc_A_txt (Rn : (BitVec 4)) (Ra : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let a : Int := (BitVec.toNat Ra)
      if (((((d == 15) || (n == 15)) || (m == 15)) || (a == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_MLS_Op_A_txt (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_MOV_rr_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:7638.29-7638.30"
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let s : Int := (BitVec.toNat Rs)
      let setflags : Bool := (S == 1#1)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if ((((d == 15) || (m == 15)) || (s == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_MOV_rr_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (s)) setflags shift_t))
  else (pure (()))


def decode_aarch32_instrs_MOV_rr_T1enc_A_txt (op : (BitVec 4)) (Rs : (BitVec 3)) (Rdm : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((! ((op == 0b0010#4) || ((op == 0b0011#4) || ((op == 0b0100#4) || (op == 0b0111#4))))) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rdm)
      let m : Int := (BitVec.toNat Rdm)
      let s : Int := (BitVec.toNat Rs)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      let setflags : Bool := (! w__1)
      let shift_t ← (( do
        (DecodeRegShift
          ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op 2)])) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                op 0)])))) ) : SailM SRType )
      (execute_aarch32_instrs_MOV_rr_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (s)) setflags shift_t))
  else (pure (()))


def decode_aarch32_instrs_MOV_rr_T2enc_A_txt (stype : (BitVec 2)) (S : (BitVec 1)) (Rm : (BitVec 4)) (Rd : (BitVec 4)) (Rs : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let s : Int := (BitVec.toNat Rs)
      let setflags : Bool := (S == 1#1)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if ((((d == 15) || (m == 15)) || (s == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_MOV_rr_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (s)) setflags shift_t))
  else (pure (()))


def decode_aarch32_instrs_MOVT_A1enc_A_txt (cond : (BitVec 4)) (imm4 : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:7730.29-7730.30"
      let d : Int := (BitVec.toNat Rd)
      let imm16 : (BitVec 16) := (imm4 +++ imm12)
      if ((d == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_MOVT_Op_A_txt (Sail.Int.toNatChecked (d)) imm16))
  else (pure (()))


def decode_aarch32_instrs_MOVT_T1enc_A_txt (i : (BitVec 1)) (imm4 : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let imm16 : (BitVec 16) := (((imm4 +++ i) +++ imm3) +++ imm8)
      if ((d == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_MOVT_Op_A_txt (Sail.Int.toNatChecked (d)) imm16))
  else (pure (()))


def decode_aarch32_instrs_MUL_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:7912.29-7912.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_MUL_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_MUL_T1enc_A_txt (Rn : (BitVec 3)) (Rdm : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rdm)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rdm)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      let setflags : Bool := (! w__1)
      (execute_aarch32_instrs_MUL_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_MUL_T2enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let setflags : Bool := false
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_MUL_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_MVN_rr_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:8202.29-8202.30"
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let s : Int := (BitVec.toNat Rs)
      let setflags : Bool := (S == 1#1)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if ((((d == 15) || (m == 15)) || (s == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_MVN_rr_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (s)) setflags shift_t))
  else (pure (()))


def decode_aarch32_instrs_ORN_i_T1enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let carry ← (( do (undefined_bitvector_at (← occLabel 3142) 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector_at (← occLabel 3143) 32) ) : SailM (BitVec 32) )
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "MVN (immediate)"))
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
      (execute_aarch32_instrs_ORN_i_Op_A_txt carry (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_ORN_r_T1enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3146) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3147) ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "MVN (register)"))
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
      (execute_aarch32_instrs_ORN_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_ORR_rr_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:8616.29-8616.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let s : Int := (BitVec.toNat Rs)
      let setflags : Bool := (S == 1#1)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if (((((d == 15) || (n == 15)) || (m == 15)) || (s == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_ORR_rr_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (s)) setflags
        shift_t))
  else (pure (()))


def decode_aarch32_instrs_PKH_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (tb : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:8660.29-8660.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 3162) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3163) ()) ) : SailM SRType )
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let tbform : Bool := (tb == 1#1)
      let w__1 ← (( do (DecodeImmShift (tb +++ 0#1) imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let shift_t := shift_t
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_PKH_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t tbform))
  else (pure (()))


def decode_aarch32_instrs_PKH_T1enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (tb : (BitVec 1)) (T : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3164) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3165) ()) ) : SailM SRType )
      if (((S == 1#1) || (T == 1#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let tbform : Bool := (tb == 1#1)
      let w__1 ← (( do (DecodeImmShift (tb +++ 0#1) (imm3 +++ imm2)) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_PKH_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t tbform))
  else (pure (()))


def decode_aarch32_instrs_PLD_i_A1enc_A_txt (U : (BitVec 1)) (R : (BitVec 1)) (Rn : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "PLD (literal)"))
      else (pure (()))
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      let is_pldw : Bool := (R == 0#1)
      (execute_aarch32_instrs_PLD_i_Op_A_txt add imm32 is_pldw (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_PLD_i_T1enc_A_txt (W : (BitVec 1)) (Rn : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "PLD (literal)"))
      else (pure (()))
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := true
      let is_pldw : Bool := (W == 1#1)
      (execute_aarch32_instrs_PLD_i_Op_A_txt add imm32 is_pldw (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_PLD_i_T2enc_A_txt (W : (BitVec 1)) (Rn : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "PLD (literal)"))
      else (pure (()))
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      let add : Bool := false
      let is_pldw : Bool := (W == 1#1)
      (execute_aarch32_instrs_PLD_i_Op_A_txt add imm32 is_pldw (Sail.Int.toNatChecked (n))))
  else (pure (()))


/-- Type quantifiers: k_add : Bool -/
def execute_aarch32_instrs_PLD_l_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) : SailM Unit := do
  let address ← (( do
    if (add : Bool)
    then
      (do
        let w__0 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
        (pure (((Align_bits w__0 4) + imm32))))
    else
      (do
        let w__1 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
        (pure (((Align_bits w__1 4) - imm32)))) ) : SailM (BitVec 32) )
  (pure ((Hint_PreloadData address)))


def decode_aarch32_instrs_PLD_r_A1enc_A_txt (U : (BitVec 1)) (R : (BitVec 1)) (Rn : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3166) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3167) ()) ) : SailM SRType )
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let add : Bool := (U == 1#1)
      let is_pldw : Bool := (R == 0#1)
      let w__1 ← (( do (DecodeImmShift stype imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if (((m == 15) || ((n == 15) && is_pldw)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let shift_t := shift_t
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_PLD_r_Op_A_txt add is_pldw (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_PLD_r_T1enc_A_txt (W : (BitVec 1)) (Rn : (BitVec 4)) (imm2 : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3168) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3169) ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "PLD (literal)"))
      else (pure (()))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let add : Bool := true
      let is_pldw : Bool := (W == 1#1)
      let (tup__0, tup__1) := ((SRType_LSL, (BitVec.toNat imm2)) : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if ((m == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_PLD_r_Op_A_txt add is_pldw (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t))
  else (pure (()))


/-- Type quantifiers: k_add : Bool, n : Nat, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_PLI_i_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (n : Nat) : SailM Unit := do
  let base ← (( do
    if ((n == 15) : Bool)
    then
      (do
        let w__0 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
        (pure ((Align_bits w__0 4))))
    else
      (do
        (R_read n)) ) : SailM (BitVec 32) )
  let address : (BitVec 32) :=
    if (add : Bool)
    then (base + imm32)
    else (base - imm32)
  (pure ((Hint_PreloadInstr address)))


def decode_aarch32_instrs_PLI_r_A1enc_A_txt (U : (BitVec 1)) (Rn : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3170) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3171) ()) ) : SailM SRType )
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let add : Bool := (U == 1#1)
      let w__1 ← (( do (DecodeImmShift stype imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if ((m == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let shift_t := shift_t
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_PLI_r_Op_A_txt add (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_PLI_r_T1enc_A_txt (Rn : (BitVec 4)) (imm2 : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3172) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3173) ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "PLI (immediate, literal)"))
      else (pure (()))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let add : Bool := true
      let (tup__0, tup__1) := ((SRType_LSL, (BitVec.toNat imm2)) : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if ((m == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_PLI_r_Op_A_txt add (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) shift_n shift_t))
  else (pure (()))


end ArmFull.Functions
