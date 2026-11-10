import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0015
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0020
import ArmFull.Fn.M0021
import ArmFull.Fn.M0044
import ArmFull.Fn.M0046
import ArmFull.Fn.M0049
import ArmFull.Fn.M0063
import ArmFull.Fn.M0086
import ArmFull.Fn.M0097
import ArmFull.Fn.M0117
import ArmFull.Fn.M0124
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0155
import ArmFull.Fn.M0169
import ArmFull.Fn.M0175
import ArmFull.Fn.M0182
import ArmFull.Fn.M0184
import ArmFull.Fn.M0196
import ArmFull.Fn.M0203
import ArmFull.Fn.M0215
import ArmFull.Fn.M0244
import ArmFull.Fn.M0245

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

def __InitSystem (_ : Unit) : SailM Unit := do
  writeReg DBGEN Signal_Low
  (TakeReset true)
  let w__0 ← (( do readReg CNTCR ) : SailM (BitVec 32) )
  writeReg CNTCR (Sail.BitVec.updateSubrange w__0 0 0 1#1)


/-- Type quantifiers: k_add : Bool, d : Nat, 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ADR_Op_A_txt (add : Bool) (d : Nat) (imm32 : (BitVec 32)) : SailM Unit := do
  let result ← (( do
    if (add : Bool)
    then
      (do
        let w__0 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
        (pure (((Align_bits w__0 4) + imm32))))
    else
      (do
        let w__1 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
        (pure (((Align_bits w__1 4) - imm32)))) ) : SailM (BitVec 32) )
  if ((d == 15) : Bool)
  then
    (do
      (ALUWritePC result))
  else
    (do
      (R_set d result))


def decode_aarch32_instrs_B_A1enc_A_txt (cond : (BitVec 4)) (imm24 : (BitVec 24)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:1401.29-1401.30"
      let imm32 : (BitVec 32) := (sign_extend (imm24 +++ 0b00#2) 32)
      (execute_aarch32_instrs_B_Op_A_txt imm32))
  else (pure (()))


def decode_aarch32_instrs_B_T1enc_A_txt (cond : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:1419.29-1419.30"
      if ((cond == 0b1110#4) : Bool)
      then sailThrow ((Error_See "UDF"))
      else (pure (()))
      if ((cond == 0b1111#4) : Bool)
      then sailThrow ((Error_See "SVC"))
      else (pure (()))
      let imm32 : (BitVec 32) := (sign_extend (imm8 +++ 0#1) 32)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_B_Op_A_txt imm32))
  else (pure (()))


def decode_aarch32_instrs_B_T2enc_A_txt (imm11 : (BitVec 11)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let imm32 : (BitVec 32) := (sign_extend (imm11 +++ 0#1) 32)
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
      (execute_aarch32_instrs_B_Op_A_txt imm32))
  else (pure (()))


def decode_aarch32_instrs_B_T3enc_A_txt (S : (BitVec 1)) (cond : (BitVec 4)) (imm6 : (BitVec 6)) (J1 : (BitVec 1)) (J2 : (BitVec 1)) (imm11 : (BitVec 11)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:1465.29-1465.30"
      if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb cond 3 1)) == 0b111#3) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      let imm32 : (BitVec 32) :=
        (sign_extend (((((S +++ J2) +++ J1) +++ imm6) +++ imm11) +++ 0#1) 32)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_B_Op_A_txt imm32))
  else (pure (()))


def decode_aarch32_instrs_B_T4enc_A_txt (S : (BitVec 1)) (imm10 : (BitVec 10)) (J1 : (BitVec 1)) (J2 : (BitVec 1)) (imm11 : (BitVec 11)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let I1 : (BitVec 1) := (Complement.complement (J1 ^^^ S))
      let I2 : (BitVec 1) := (Complement.complement (J2 ^^^ S))
      let imm32 : (BitVec 32) :=
        (sign_extend (((((S +++ I1) +++ I2) +++ imm10) +++ imm11) +++ 0#1) 32)
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
      (execute_aarch32_instrs_B_Op_A_txt imm32))
  else (pure (()))


def decode_aarch32_instrs_BL_i_A1enc_A_txt (cond : (BitVec 4)) (imm24 : (BitVec 24)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:1968.29-1968.30"
      let imm32 : (BitVec 32) := (sign_extend (imm24 +++ 0b00#2) 32)
      let targetInstrSet : InstrSet := InstrSet_A32
      (execute_aarch32_instrs_BL_i_Op_A_txt imm32 targetInstrSet))
  else (pure (()))


def decode_aarch32_instrs_BL_i_A2enc_A_txt (H : (BitVec 1)) (imm24 : (BitVec 24)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let imm32 : (BitVec 32) := (sign_extend ((imm24 +++ H) +++ 0#1) 32)
      let targetInstrSet : InstrSet := InstrSet_T32
      (execute_aarch32_instrs_BL_i_Op_A_txt imm32 targetInstrSet))
  else (pure (()))


def decode_aarch32_instrs_BL_i_T1enc_A_txt (S : (BitVec 1)) (imm10 : (BitVec 10)) (J1 : (BitVec 1)) (J2 : (BitVec 1)) (imm11 : (BitVec 11)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let I1 : (BitVec 1) := (Complement.complement (J1 ^^^ S))
      let I2 : (BitVec 1) := (Complement.complement (J2 ^^^ S))
      let imm32 : (BitVec 32) :=
        (sign_extend (((((S +++ I1) +++ I2) +++ imm10) +++ imm11) +++ 0#1) 32)
      let targetInstrSet : InstrSet := InstrSet_T32
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
      (execute_aarch32_instrs_BL_i_Op_A_txt imm32 targetInstrSet))
  else (pure (()))


def decode_aarch32_instrs_BL_i_T2enc_A_txt (S : (BitVec 1)) (imm10H : (BitVec 10)) (J1 : (BitVec 1)) (J2 : (BitVec 1)) (imm10L : (BitVec 10)) (H : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((H == 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let I1 : (BitVec 1) := (Complement.complement (J1 ^^^ S))
      let I2 : (BitVec 1) := (Complement.complement (J2 ^^^ S))
      let imm32 : (BitVec 32) :=
        (sign_extend (((((S +++ I1) +++ I2) +++ imm10H) +++ imm10L) +++ 0b00#2) 32)
      let targetInstrSet : InstrSet := InstrSet_A32
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
      (execute_aarch32_instrs_BL_i_Op_A_txt imm32 targetInstrSet))
  else (pure (()))


def decode_aarch32_instrs_BLX_r_A1enc_A_txt (cond : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:2077.29-2077.30"
      let m : Int := (BitVec.toNat Rm)
      if ((m == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_BLX_r_Op_A_txt (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_BLX_r_T1enc_A_txt (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let m : Int := (BitVec.toNat Rm)
      if ((m == 15) : Bool)
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
      (execute_aarch32_instrs_BLX_r_Op_A_txt (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_BX_A1enc_A_txt (cond : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:2135.29-2135.30"
      let m : Int := (BitVec.toNat Rm)
      (execute_aarch32_instrs_BX_Op_A_txt (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_BX_T1enc_A_txt (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let m : Int := (BitVec.toNat Rm)
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
      (execute_aarch32_instrs_BX_Op_A_txt (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_BXJ_A1enc_A_txt (cond : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:2187.29-2187.30"
      let m : Int := (BitVec.toNat Rm)
      if ((m == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_BXJ_Op_A_txt (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_BXJ_T1enc_A_txt (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let m : Int := (BitVec.toNat Rm)
      if ((m == 15) : Bool)
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
      (execute_aarch32_instrs_BXJ_Op_A_txt (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_CBNZ_T1enc_A_txt (op : (BitVec 1)) (i : (BitVec 1)) (imm5 : (BitVec 5)) (Rn : (BitVec 3)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend ((i +++ imm5) +++ 0#1) 32)
  let nonzero : Bool := (op == 1#1)
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  (execute_aarch32_instrs_CBNZ_Op_A_txt imm32 (Sail.Int.toNatChecked (n)) nonzero)


/-- Type quantifiers: k_nXS : Bool -/
def execute_aarch64_instrs_system_barriers_dsb (alias' : DSBAlias) (domain : MBReqDomain) (nXS__arg : Bool) (types : MBReqTypes) : SailM Unit := do
  let nXS : Bool := nXS__arg
  match alias' with
  | .DSBAlias_SSBB =>
    (do
      (SpeculativeStoreBypassBarrierToVA ()))
  | .DSBAlias_PSSBB => (pure ((SpeculativeStoreBypassBarrierToPA ())))
  | .DSBAlias_DSB =>
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
      let w__4 ← (( do
        if (((! nXS) : Bool) : Bool)
        then
          (do
            (HaveFeatXS ()))
        else (pure false) ) : SailM Bool )
      let nXS ← (( do
        if (w__4 : Bool)
        then
          (do
            if ((← do
                 if ((← do
                      if ((← do
                           let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
                           (pure (((w__5.EL == EL0) : Bool)))) : Bool)
                      then (pure true)
                      else
                        (do
                          let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
                          (pure (((w__6.EL == EL1) : Bool))))) : Bool)
                 then
                   (do
                     (IsHCRXEL2Enabled ()))
                 else (pure false)) : Bool)
            then
              (do
                let w__10 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_HCRX_EL2_Type_FnXS w__10) == 1#1) : Bool))))
            else (pure false))
        else (pure (nXS)) ) : SailM Bool )
      (DataSynchronizationBarrier domain types nXS))


def decode_tcancel_aarch64_instrs_system_tme_tcancel (imm16 : (BitVec 16)) : SailM Unit := do
  let w__0 ← (( do (HaveTME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let retry : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm16 15)])) == 1#1)
  let reason : (BitVec 15) := (Sail.BitVec.extractLsb imm16 14 0)
  (execute_aarch64_instrs_system_tme_tcancel reason retry)


def Halt (reason : (BitVec 6)) : SailM Unit := do
  let is_async : Bool := false
  (Halt__1 reason is_async)


def GranuleProtectionCheck (addrdesc : AddressDescriptor) (accdesc : AccessDescriptor) : SailM GPCFRecord := SailME.run do
  let gpcf ← (( do (undefined_GPCFRecord (← occLabel 1242) ()) ) : SailME GPCFRecord GPCFRecord
    )
  let gpt_entry ← (( do (undefined_GPTEntry (← occLabel 1243) ()) ) : SailME GPCFRecord GPTEntry
    )
  let w__0 ← (( do (HaveRME ()) ) : SailME GPCFRecord Bool )
  ArmFull.assert w__0 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:19882.20-19882.21"
  let w__2 ← (( do
    (pure ((← do
          readReg __tlb_enabled) && ((bne accdesc.acctype AccessType_TTW) : Bool))) ) : SailME
    GPCFRecord Bool )
  if (w__2 : Bool)
  then
    (do
      let w__3 ← (( do (TLBIncludesGPT addrdesc.tlbcontext) ) : SailME GPCFRecord Bool )
      if (w__3 : Bool)
      then
        (do
          let w__4 ← (( do (GPCNoFault ()) ) : SailME GPCFRecord GPCFRecord )
          SailME.throw (w__4 : GPCFRecord))
      else (pure (())))
  else (pure (()))
  let address : FullAddress := addrdesc.paddress
  let w__5 ← (( do readReg GPCCR_EL3 ) : SailME GPCFRecord (BitVec 64) )
  if (((_get_GPCCR_EL3_Type_GPC w__5) == 0#1) : Bool)
  then
    (do
      let w__6 ← (( do readReg __tlb_enabled ) : SailME GPCFRecord Bool )
      let _ : Unit :=
        if (w__6 : Bool)
        then (SetTLBIncludesGPT addrdesc.tlbcontext 56)
        else ()
      (GPCNoFault ()))
  else
    (do
      let w__8 ← (( do (GPCRegistersConsistent ()) ) : SailME GPCFRecord Bool )
      if ((! w__8) : Bool)
      then
        (do
          (GPCFault GPCF_Walk 0))
      else
        (do
          let w__10 ← (( do (AbovePPS address.address) ) : SailME GPCFRecord Bool )
          if (w__10 : Bool)
          then
            (do
              if ((BEq.beq address.paspace PAS_NonSecure) : Bool)
              then
                (do
                  let w__12 ← (( do
                    (pure ((← do
                          readReg __tlb_enabled) && ((bne accdesc.acctype AccessType_TTW) : Bool)))
                    ) : SailME GPCFRecord Bool )
                  let _ : Unit :=
                    if (w__12 : Bool)
                    then (SetTLBIncludesGPT addrdesc.tlbcontext 56)
                    else ()
                  (GPCNoFault ()))
              else
                (do
                  (GPCFault GPCF_Fail 0)))
          else
            (do
              let w__16 ← (( do readReg GPTBR_EL3 ) : SailME GPCFRecord (BitVec 64) )
              let gpt_base : (BitVec 56) :=
                (Sail.BitVec.zeroExtend ((_get_GPTBR_EL3_Type_BADDR w__16) +++ (Zeros (n := 12))) 56)
              let w__17 ← (( do (AbovePPS gpt_base) ) : SailME GPCFRecord Bool )
              if (w__17 : Bool)
              then
                (do
                  (GPCFault GPCF_AddressSize 0))
              else
                (do
                  let w__19 ← (( do (GPTWalk address.address accdesc) ) : SailME GPCFRecord
                    (GPCFRecord × GPTEntry) )
                  let (tup__0, tup__1) := (w__19 : (GPCFRecord × GPTEntry))
                  let gpcf : GPCFRecord := tup__0
                  let gpt_entry : GPTEntry := tup__1
                  if ((bne gpcf.gpf GPCF_None) : Bool)
                  then (pure (gpcf))
                  else
                    (do
                      let permitted ← (( do (GPICheck address.paspace gpt_entry.gpi) ) : SailME
                        GPCFRecord Bool )
                      if ((! permitted) : Bool)
                      then
                        (do
                          (GPCFault GPCF_Fail gpt_entry.level))
                      else
                        (do
                          let w__21 ← (( do
                            (pure ((← do
                                  readReg __tlb_enabled) && ((bne accdesc.acctype AccessType_TTW) : Bool)))
                            ) : SailME GPCFRecord Bool )
                          let _ : Unit :=
                            if (w__21 : Bool)
                            then (SetTLBIncludesGPT addrdesc.tlbcontext gpt_entry.contig_size)
                            else ()
                          (GPCNoFault ())))))))


def CheckPendingResetCatch (_ : Unit) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         (HaltingAllowed ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg EDESR ) : SailM (BitVec 32) )
        (pure ((((_get_EDESR_Type_RC w__1) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let is_async : Bool := true
      (Halt__1 DebugHalt_ResetCatch is_async))
  else (pure (()))


def CheckPendingOSUnlockCatch (_ : Unit) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         (HaltingAllowed ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg EDESR ) : SailM (BitVec 32) )
        (pure ((((_get_EDESR_Type_OSUC w__1) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let is_async : Bool := true
      (Halt__1 DebugHalt_OSUnlockCatch is_async))
  else (pure (()))


/-- Type quantifiers: k_is_async : Bool -/
def CheckPendingExceptionCatch (is_async : Bool) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         if ((← do
              (Havev8p8Debug ())) : Bool)
         then
           (do
             (HaltingAllowed ()))
         else (pure false)) : Bool)
    then
      (do
        let w__3 ← (( do readReg EDESR ) : SailM (BitVec 32) )
        (pure ((((_get_EDESR_Type_EC w__3) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      (Halt__1 DebugHalt_ExceptionCatch is_async))
  else (pure (()))


def decode_aarch32_instrs_ADR_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:951.29-951.30"
      let d : Int := (BitVec.toNat Rd)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      let add : Bool := true
      (execute_aarch32_instrs_ADR_Op_A_txt add (Sail.Int.toNatChecked (d)) imm32))
  else (pure (()))


def decode_aarch32_instrs_ADR_A2enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:972.29-972.30"
      let d : Int := (BitVec.toNat Rd)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      let add : Bool := false
      (execute_aarch32_instrs_ADR_Op_A_txt add (Sail.Int.toNatChecked (d)) imm32))
  else (pure (()))


def decode_aarch32_instrs_ADR_T1enc_A_txt (Rd : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let add : Bool := true
      (execute_aarch32_instrs_ADR_Op_A_txt add (Sail.Int.toNatChecked (d)) imm32))
  else (pure (()))


def decode_aarch32_instrs_ADR_T2enc_A_txt (i : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend ((i +++ imm3) +++ imm8) 32)
      let add : Bool := false
      if ((d == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_ADR_Op_A_txt add (Sail.Int.toNatChecked (d)) imm32))
  else (pure (()))


def decode_aarch32_instrs_ADR_T3enc_A_txt (i : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend ((i +++ imm3) +++ imm8) 32)
      let add : Bool := true
      if ((d == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_ADR_Op_A_txt add (Sail.Int.toNatChecked (d)) imm32))
  else (pure (()))


def execute_aarch32_instrs_HLT_Op_A_txt (_ : Unit) : SailM Unit := do
  let is_async : Bool := false
  (Halt__1 DebugHalt_HaltInstruction is_async)


def decode_dsb_aarch64_instrs_system_barriers_dsb (opc : (BitVec 2)) (CRm : (BitVec 4)) : SailM Unit := do
  let nXS : Bool := false
  let alias' ← (( do (undefined_DSBAlias (← occLabel 4098) ()) ) : SailM DSBAlias )
  let alias' : DSBAlias :=
    match CRm with
    | 0b0000 => DSBAlias_SSBB
    | 0b0100 => DSBAlias_PSSBB
    | _ => DSBAlias_DSB
  let alias' := alias'
  let domain ← (( do (undefined_MBReqDomain (← occLabel 4099) ()) ) : SailM MBReqDomain )
  let domain : MBReqDomain :=
    match (BitVec.setWidth 2 (Sail.BitVec.extractLsb CRm 3 2)) with
    | 0b00 => MBReqDomain_OuterShareable
    | 0b01 => MBReqDomain_Nonshareable
    | 0b10 => MBReqDomain_InnerShareable
    | _ => MBReqDomain_FullSystem
  let types ← (( do (undefined_MBReqTypes (← occLabel 4100) ()) ) : SailM MBReqTypes )
  let (domain, types) : (MBReqDomain × MBReqTypes) :=
    match (BitVec.setWidth 2 (Sail.BitVec.extractLsb CRm 1 0)) with
    | 0b00 =>
      (let types : MBReqTypes := MBReqTypes_All
      let domain : MBReqDomain := MBReqDomain_FullSystem
      (domain, types))
    | 0b01 =>
      (let types : MBReqTypes := MBReqTypes_Reads
      (domain, types))
    | 0b10 =>
      (let types : MBReqTypes := MBReqTypes_Writes
      (domain, types))
    | _ =>
      (let types : MBReqTypes := MBReqTypes_All
      (domain, types))
  (execute_aarch64_instrs_system_barriers_dsb alias' domain nXS types)


end ArmFull.Functions
