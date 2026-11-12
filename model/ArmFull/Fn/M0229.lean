import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0042
import ArmFull.Fn.M0124
import ArmFull.Fn.M0150
import ArmFull.Fn.M0169
import ArmFull.Fn.M0175
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0216
import ArmFull.Fn.M0220
import ArmFull.Fn.M0221
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

def AArch32_PendingUnmaskedVirtualInterrupts (_ : Unit) : SailM (Bool × Bool × Bool) := do
  let w__4 ← (( do
    if ((← do
         if (((HaveEL EL2) : Bool) : Bool)
         then
           (do
             let w__0 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
             (pure (((! w__0) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        if (((HaveEL EL3) : Bool) : Bool)
        then
          (do
            let w__2 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
            (pure (((! w__2) : Bool))))
        else (pure false)) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      (AArch64_PendingUnmaskedVirtualInterrupts (w__5.A +++ (w__6.I +++ w__7.F))))
  else
    (do
      let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
      let mask : (BitVec 3) := (w__9.A +++ (w__10.I +++ w__11.F))
      let pending ← (( do (undefined_bitvector_at (← occLabel 2870) 3) ) : SailM (BitVec 3) )
      let w__18 ← (( do
        if ((← do
             if ((← do
                  if ((← do
                       let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
                       (pure (((w__12.EL == EL0) : Bool)))) : Bool)
                  then (pure true)
                  else
                    (do
                      let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
                      (pure (((w__13.EL == EL1) : Bool))))) : Bool)
             then
               (do
                 (EL2Enabled ()))
             else (pure false)) : Bool)
        then
          (do
            let w__17 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
            (pure ((((_get_HCR_Type_TGE w__17) == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      let pending ← (( do
        if (w__18 : Bool)
        then
          (do
            let w__19 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
            let w__20 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
            let w__21 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
            let w__22 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
            let w__23 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
            let w__24 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
            let pending :=
              ((((_get_HCR_Type_VA w__19) +++ ((_get_HCR_Type_VI w__20) +++ (_get_HCR_Type_VF w__21))) &&& ((_get_HCR_Type_AMO
                    w__22) +++ ((_get_HCR_Type_IMO w__23) +++ (_get_HCR_Type_FMO w__24)))) : (BitVec 3))
            (pure (pending)))
        else (pure (0b000#3)) ) : SailM (BitVec 3) )
      let unmasked_pending : (BitVec 3) := (pending &&& (Complement.complement mask))
      (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access unmasked_pending 2)])) == 1#1), ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
              unmasked_pending 1)])) == 1#1), ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
              unmasked_pending 0)])) == 1#1)))))


def __UpdateSystemCounter (_ : Unit) : SailM Unit := do
  (GenericCounterTick ())


def decode_aarch32_instrs_ADC_rr_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:252.29-252.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let s : Int := (BitVec.toNat Rs)
      let setflags : Bool := (S == 1#1)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if (((((d == 15) || (n == 15)) || (m == 15)) || (s == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_ADC_rr_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (s)) setflags
        shift_t))
  else (pure (()))


def decode_aarch32_instrs_ADD_i_T1enc_A_txt (imm3 : (BitVec 3)) (Rn : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      let setflags : Bool := (! w__1)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm3 32)
      (execute_aarch32_instrs_ADD_i_OpT_A_txt (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_ADD_i_T2enc_A_txt (Rdn : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rdn)
      let n : Int := (BitVec.toNat Rdn)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      let setflags : Bool := (! w__1)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      (execute_aarch32_instrs_ADD_i_OpT_A_txt (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_ADD_i_T3enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then sailThrow ((Error_See "CMN (immediate)"))
      else (pure (()))
      if ((Rn == 0b1101#4) : Bool)
      then sailThrow ((Error_See "ADD (SP plus immediate)"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (T32ExpandImm ((i +++ imm3) +++ imm8)) ) : SailM (BitVec 32) )
      if ((((d == 15) && (! setflags)) || (n == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_ADD_i_OpT_A_txt (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_ADD_i_T4enc_A_txt (i : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "ADR"))
      else (pure (()))
      if ((Rn == 0b1101#4) : Bool)
      then sailThrow ((Error_See "ADD (SP plus immediate)"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let setflags : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend ((i +++ imm3) +++ imm8) 32)
      if ((d == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_ADD_i_OpT_A_txt (Sail.Int.toNatChecked (d)) imm32
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_ADD_rr_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:632.29-632.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let s : Int := (BitVec.toNat Rs)
      let setflags : Bool := (S == 1#1)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if (((((d == 15) || (n == 15)) || (m == 15)) || (s == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_ADD_rr_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (s)) setflags
        shift_t))
  else (pure (()))


def decode_aarch32_instrs_AND_rr_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:1279.29-1279.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let s : Int := (BitVec.toNat Rs)
      let setflags : Bool := (S == 1#1)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if (((((d == 15) || (n == 15)) || (m == 15)) || (s == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_AND_rr_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (s)) setflags
        shift_t))
  else (pure (()))


def decode_aarch32_instrs_ASR_i_T1enc_A_txt (imm5 : (BitVec 5)) (Rm : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 2964) ()) ) : SailM Int )
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      let setflags : Bool := (! w__1)
      let (_, __tup_1) ← (( do (DecodeImmShift 0b10#2 imm5) ) : SailM (SRType × Int) )
      let shift_n : Int := __tup_1
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_ASR_i_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        setflags shift_n))
  else (pure (()))


def decode_aarch32_instrs_ASR_r_T1enc_A_txt (Rm : (BitVec 3)) (Rdn : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rdn)
      let n : Int := (BitVec.toNat Rdn)
      let m : Int := (BitVec.toNat Rm)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      let setflags : Bool := (! w__1)
      (execute_aarch32_instrs_ASR_r_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) setflags))
  else (pure (()))


def decode_aarch32_instrs_BFC_A1enc_A_txt (cond : (BitVec 4)) (msb : (BitVec 5)) (Rd : (BitVec 4)) (lsb : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:1527.29-1527.30"
      let d : Int := (BitVec.toNat Rd)
      let msbit : Int := (BitVec.toNat msb)
      let lsbit : Int := (BitVec.toNat lsb)
      if ((d == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((msbit <b lsbit) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_BFC_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (lsbit)) (Sail.Int.toNatChecked (msbit))))
  else (pure (()))


def decode_aarch32_instrs_BFC_T1enc_A_txt (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (msb : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let msbit : Int := (BitVec.toNat msb)
      let lsbit : Int := (BitVec.toNat (imm3 +++ imm2))
      if ((d == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((msbit <b lsbit) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_BFC_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (lsbit)) (Sail.Int.toNatChecked (msbit))))
  else (pure (()))


def decode_aarch32_instrs_BFI_A1enc_A_txt (cond : (BitVec 4)) (msb : (BitVec 5)) (Rd : (BitVec 4)) (lsb : (BitVec 5)) (Rn : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:1595.29-1595.30"
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "BFC"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let msbit : Int := (BitVec.toNat msb)
      let lsbit : Int := (BitVec.toNat lsb)
      if ((d == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((msbit <b lsbit) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_BFI_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (lsbit)) (Sail.Int.toNatChecked (msbit)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_BFI_T1enc_A_txt (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (msb : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "BFC"))
      else (pure (()))
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let msbit : Int := (BitVec.toNat msb)
      let lsbit : Int := (BitVec.toNat (imm3 +++ imm2))
      if ((d == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((msbit <b lsbit) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_BFI_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (lsbit)) (Sail.Int.toNatChecked (msbit)) (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_BIC_rr_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:1881.29-1881.30"
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let s : Int := (BitVec.toNat Rs)
      let setflags : Bool := (S == 1#1)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if (((((d == 15) || (n == 15)) || (m == 15)) || (s == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_BIC_rr_Op_A_txt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (s)) setflags
        shift_t))
  else (pure (()))


def decode_aarch32_instrs_CLZ_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:2321.29-2321.30"
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      if (((d == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_CLZ_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_CLZ_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let m : Int := (BitVec.toNat Rm)
      let n : Int := (BitVec.toNat Rn)
      if ((((m != n) || (d == 15)) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_CLZ_Op_A_txt (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_CMN_i_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:2381.29-2381.30"
      let n : Int := (BitVec.toNat Rn)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      (execute_aarch32_instrs_CMN_i_Op_A_txt imm32 (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_CMN_i_T1enc_A_txt (i : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let n : Int := (BitVec.toNat Rn)
      let imm32 ← (( do (T32ExpandImm ((i +++ imm3) +++ imm8)) ) : SailM (BitVec 32) )
      if ((n == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_CMN_i_Op_A_txt imm32 (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_CMN_r_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:2440.29-2440.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 2987) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 2988) ()) ) : SailM SRType )
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let w__1 ← (( do (DecodeImmShift stype imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_CMN_r_Op_A_txt (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_CMN_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 2989) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 2990) ()) ) : SailM SRType )
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
      let shift_t : SRType := tup__0
      let shift_n : Int := (Sail.Int.toNatChecked (tup__1))
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_CMN_r_Op_A_txt (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_CMN_r_T2enc_A_txt (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 2991) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 2992) ()) ) : SailM SRType )
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let w__1 ← (( do (DecodeImmShift stype (imm3 +++ imm2)) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if (((n == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let shift_t := shift_t
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_CMN_r_Op_A_txt (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_CMN_rr_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:2539.29-2539.30"
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let s : Int := (BitVec.toNat Rs)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if ((((n == 15) || (m == 15)) || (s == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_CMN_rr_Op_A_txt (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (s)) shift_t))
  else (pure (()))


def decode_aarch32_instrs_CMP_i_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:2580.29-2580.30"
      let n : Int := (BitVec.toNat Rn)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      (execute_aarch32_instrs_CMP_i_Op_A_txt imm32 (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_CMP_i_T1enc_A_txt (Rn : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      (execute_aarch32_instrs_CMP_i_Op_A_txt imm32 (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_CMP_i_T2enc_A_txt (i : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let n : Int := (BitVec.toNat Rn)
      let imm32 ← (( do (T32ExpandImm ((i +++ imm3) +++ imm8)) ) : SailM (BitVec 32) )
      if ((n == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_CMP_i_Op_A_txt imm32 (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_CMP_r_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:2657.29-2657.30"
      let shift_n ← (( do (undefined_int_at (← occLabel 2999) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3000) ()) ) : SailM SRType )
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let w__1 ← (( do (DecodeImmShift stype imm5) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_CMP_r_Op_A_txt (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_CMP_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3001) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3002) ()) ) : SailM SRType )
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
      let shift_t : SRType := tup__0
      let shift_n : Int := (Sail.Int.toNatChecked (tup__1))
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_CMP_r_Op_A_txt (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_CMP_r_T2enc_A_txt (N : (BitVec 1)) (Rm : (BitVec 4)) (Rn : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3003) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3004) ()) ) : SailM SRType )
      let n : Int := (BitVec.toNat (N +++ Rn))
      let m : Int := (BitVec.toNat Rm)
      let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
      let shift_t : SRType := tup__0
      let shift_n : Int := (Sail.Int.toNatChecked (tup__1))
      let shift_n : Int := shift_n
      if (((n <b 8) && (m <b 8)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((n == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let shift_t := shift_t
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_CMP_r_Op_A_txt (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_CMP_r_T3enc_A_txt (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int_at (← occLabel 3005) ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType (← occLabel 3006) ()) ) : SailM SRType )
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let w__1 ← (( do (DecodeImmShift stype (imm3 +++ imm2)) ) : SailM (SRType × Int) )
      let (tup__0, tup__1) := (w__1 : (SRType × Int))
      let shift_t : SRType := tup__0
      let shift_n : Int := tup__1
      let shift_n : Int := shift_n
      if (((n == 15) || (m == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let shift_t := shift_t
      let shift_n : Int := shift_n
      (execute_aarch32_instrs_CMP_r_Op_A_txt (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        shift_n shift_t))
  else (pure (()))


def decode_aarch32_instrs_CMP_rr_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-arm/instrs32.sail:2787.29-2787.30"
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let s : Int := (BitVec.toNat Rs)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if ((((n == 15) || (m == 15)) || (s == 15)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_CMP_rr_Op_A_txt (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (s)) shift_t))
  else (pure (()))


end ArmFull.Functions
