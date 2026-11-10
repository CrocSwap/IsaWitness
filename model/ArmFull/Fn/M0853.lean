import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0008
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0034
import ArmFull.Fn.M0041
import ArmFull.Fn.M0043
import ArmFull.Fn.M0045
import ArmFull.Fn.M0047
import ArmFull.Fn.M0049
import ArmFull.Fn.M0053
import ArmFull.Fn.M0080
import ArmFull.Fn.M0087
import ArmFull.Fn.M0114
import ArmFull.Fn.M0124
import ArmFull.Fn.M0142
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0154
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0182
import ArmFull.Fn.M0186
import ArmFull.Fn.M0203
import ArmFull.Fn.M0215
import ArmFull.Fn.M0220
import ArmFull.Fn.M0228
import ArmFull.Fn.M0254
import ArmFull.Fn.M0582
import ArmFull.Fn.M0583
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

/-- Type quantifiers: k_advsimd : Bool, k_fpexc_check : Bool -/
def AArch32_CheckAdvSIMDOrFPEnabled (fpexc_check : Bool) (advsimd : Bool) : SailM Unit := do
  let cpacr_asedis ← (( do (undefined_bitvector_at (← occLabel 2717) 1) ) : SailM (BitVec 1) )
  let cpacr_cp10 ← (( do (undefined_bitvector_at (← occLabel 2718) 2) ) : SailM (BitVec 2) )
  let fpexc_en ← (( do (undefined_bitvector_at (← occLabel 2719) 1) ) : SailM (BitVec 1) )
  let w__8 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__0.EL == EL0) : Bool)))) : Bool)
         then
           (do
             let w__1 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
             (pure (((! w__1) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        if ((← do
             let w__3 ← (( do (EL2Enabled ()) ) : SailM Bool )
             (pure (((! w__3) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 let w__4 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                 (pure (((! w__4) : Bool)))) : Bool)
            then
              (do
                let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_HCR_EL2_Type_TGE w__5) == 0#1) : Bool))))
            else (pure false)))
    else (pure false) ) : SailM Bool )
  if (w__8 : Bool)
  then
    (do
      (AArch64_CheckFPEnabled ())
      (AArch64_CheckFPAdvSIMDEnabled ()))
  else
    (do
      let w__17 ← (( do
        if ((← do
             if ((← do
                  if ((← do
                       if ((← do
                            let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
                            (pure (((w__9.EL == EL0) : Bool)))) : Bool)
                       then
                         (do
                           (EL2Enabled ()))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__12 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__12) : Bool))))
                  else (pure false)) : Bool)
             then
               (do
                 let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                 (pure ((((_get_HCR_EL2_Type_TGE w__14) == 1#1) : Bool))))
             else (pure false)) : Bool)
        then
          (do
            let w__16 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
            (pure (((! w__16) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__17 : Bool)
      then
        (do
          let w__19 ← (( do
            if ((fpexc_check : Bool) : Bool)
            then
              (do
                let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_HCR_EL2_Type_RW w__18) == 0#1) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__19 : Bool)
          then
            (do
              let fpexc_en ← (( do (__IMPDEF_bits 1 "FPEXC.EN value when TGE==1 and RW==0") ) :
                SailM (BitVec 1) )
              if ((fpexc_en == 0#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else (pure (())))
          else (pure (()))
          (AArch64_CheckFPEnabled ()))
      else
        (do
          let w__20 ← (( do (CPACR_read__1 ()) ) : SailM (BitVec 32) )
          let cpacr_asedis : (BitVec 1) := ((_get_CPACR_Type_ASEDIS w__20) : (BitVec 1))
          let w__21 ← (( do (CPACR_read__1 ()) ) : SailM (BitVec 32) )
          let cpacr_cp10 : (BitVec 2) := ((_get_CPACR_Type_cp10 w__21) : (BitVec 2))
          let w__25 ← (( do
            if ((← do
                 if (((HaveEL EL3) : Bool) : Bool)
                 then
                   (do
                     (ELUsingAArch32 EL3))
                 else (pure false)) : Bool)
            then
              (do
                let w__24 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
                (pure (((BEq.beq w__24 SS_NonSecure) : Bool))))
            else (pure false) ) : SailM Bool )
          let (cpacr_asedis, cpacr_cp10) ← (( do
            if (w__25 : Bool)
            then
              (do
                let w__26 ← (( do readReg NSACR ) : SailM (BitVec 32) )
                let cpacr_asedis : (BitVec 1) :=
                  if (((_get_NSACR_Type_NSASEDIS w__26) == 1#1) : Bool)
                  then 1#1
                  else cpacr_asedis
                let w__27 ← (( do readReg NSACR ) : SailM (BitVec 32) )
                let cpacr_cp10 : (BitVec 2) :=
                  if (((_get_NSACR_Type_cp10 w__27) == 0#1) : Bool)
                  then 0b00#2
                  else cpacr_cp10
                (pure ((cpacr_asedis, cpacr_cp10))))
            else (pure ((cpacr_asedis, cpacr_cp10))) ) : SailM ((BitVec 1) × (BitVec 2)) )
          let w__28 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((w__28.EL != EL2) : Bool)
          then
            (do
              if ((advsimd && (cpacr_asedis == 1#1)) : Bool)
              then sailThrow ((Error_Undefined ()))
              else (pure (()))
              let disabled ← (( do (undefined_bool_at (← occLabel 2720) ()) ) : SailM Bool )
              let disabled ← (( do
                match cpacr_cp10 with
                | 0b00 => (pure (true))
                | 0b01 =>
                  (do
                    let w__29 ← (( do readReg PSTATE ) : SailM ProcState )
                    let disabled := ((w__29.EL == EL0) : Bool)
                    (pure (disabled)))
                | 0b10 =>
                  (do
                    (ConstrainUnpredictableBool Unpredictable_RESCPACR))
                | _ => (pure (false)) ) : SailM Bool )
              let disabled := disabled
              if (disabled : Bool)
              then sailThrow ((Error_Undefined ()))
              else (pure (())))
          else (pure (()))
          let w__32 ← (( do
            if ((fpexc_check : Bool) : Bool)
            then
              (do
                let w__31 ← (( do (FPEXC_read ()) ) : SailM (BitVec 32) )
                (pure ((((_get_FPEXC_Type_EN w__31) == 0#1) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__32 : Bool)
          then sailThrow ((Error_Undefined ()))
          else (pure (()))
          (AArch32_CheckFPAdvSIMDTrap advsimd)))


/-- Type quantifiers: k_read : Bool, t : Int -/
def AArch32_UnallocatedSysRegAccess (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (read : Bool) (t : Int) : SailM Unit := SailME.run do
  let tid3_trap : Bool := false
  let w__6 ← (( do
    if ((← do
         if ((← do
              (pure ((← do
                    let w__0 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                    let w__1 ← (( do (PLOfEL w__0.EL) ) : SailME Unit PrivilegeLevel )
                    (pure (((BEq.beq w__1 PL1) : Bool)))) && (read : Bool)))) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__5 ← (( do readReg HCR_EL2 ) : SailME Unit (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_TID3 w__5) == 1#1) : Bool))))
    else (pure false) ) : SailME Unit Bool )
  let tid3_trap ← (( do
    if (w__6 : Bool)
    then
      (do
        let w__7 ← (( do (HaveFGTExt ()) ) : SailME Unit Bool )
        if (w__7 : Bool)
        then (pure (true))
        else
          (do
            (__IMPDEF_boolean "Unallocated encodings trapped by HCR_EL2.TID3")))
    else (pure (tid3_trap)) ) : SailME Unit Bool )
  if (((((tid3_trap && (((BitVec.toNat coproc) == 15) : Bool)) && (((BitVec.toNat opc1) == 0) : Bool)) && (((BitVec.toNat
             CRn) == 0) : Bool)) && ((((BitVec.toNat CRm) == 2) || ((((BitVec.toNat CRm) == 3) || ((((BitVec.toNat
                 CRm) == 4) || ((((BitVec.toNat CRm) == 5) || ((((BitVec.toNat CRm) == 6) || (((BitVec.toNat
                     CRm) == 7) : Bool)) : Bool)) : Bool)) : Bool)) : Bool)) : Bool)) : Bool)
  then
    (do
      let w__10 ← (( do (ELUsingAArch32 EL2) ) : SailME Unit Bool )
      if (w__10 : Bool)
      then
        (do
          (AArch32_SystemAccessTrap M32_Hyp (BitVec.toNat 0x3#4)))
      else
        (do
          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x3#4))))
  else (pure (()))
  let w__11 ← (( do (GetNreg ()) ) : SailME Unit Int )
  (AArch32_CheckCP15InstrCoarseTraps (BitVec.toNat CRn) w__11 (BitVec.toNat CRm))
  if (((((((BitVec.toNat coproc) == 15) && (opc1 == 0b000#3)) && (CRn == 0b0000#4)) && (CRm == 0b0010#4)) && (opc2 == 0b111#3)) : Bool)
  then
    (do
      let w__13 ← (( do
        (pure ((← do
              let w__12 ← (( do readReg PSTATE ) : SailME Unit ProcState )
              (pure (((w__12.EL != EL0) : Bool)))) && (read : Bool))) ) : SailME Unit Bool )
      if (w__13 : Bool)
      then
        (do
          let w__14 ← (( do (__UNKNOWN_bits 32) ) : SailME Unit (BitVec 32) )
          (R_set t w__14)
          SailME.throw (() : Unit))
      else sailThrow ((Error_Undefined ())))
  else (pure (()))
  if ((((((BitVec.toNat coproc) == 15) && (opc1 == 0b000#3)) && (CRn == 0b0000#4)) && (((BitVec.toNat
           CRm) ≥b 3) : Bool)) : Bool)
  then
    (do
      let w__16 ← (( do
        (pure ((← do
              let w__15 ← (( do readReg PSTATE ) : SailME Unit ProcState )
              (pure (((w__15.EL != EL0) : Bool)))) && (read : Bool))) ) : SailME Unit Bool )
      if (w__16 : Bool)
      then
        (do
          let w__17 ← (( do (__UNKNOWN_bits 32) ) : SailME Unit (BitVec 32) )
          (R_set t w__17)
          SailME.throw (() : Unit))
      else sailThrow ((Error_Undefined ())))
  else (pure (()))
  if ((! read) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((((BitVec.toNat coproc) == 15) && (CRn == 0b0000#4)) : Bool)
  then
    (do
      if (((BitVec.toNat opc1) >b 0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if (((CRm == 0b0011#4) && ((opc2 == 0b000#3) || ((opc2 == 0b001#3) || (opc2 == 0b010#3)))) : Bool)
          then
            (do
              let w__18 ← (( do (__UNKNOWN_bits 32) ) : SailME Unit (BitVec 32) )
              (R_set t w__18))
          else
            (do
              if ((((CRm == 0b0100#4) || ((CRm == 0b0110#4) || (CRm == 0b0111#4))) && ((opc2 == 0b000#3) || ((opc2 == 0b001#3) || (opc2 == 0b111#3)))) : Bool)
              then
                (do
                  let w__19 ← (( do (__UNKNOWN_bits 32) ) : SailME Unit (BitVec 32) )
                  (R_set t w__19))
              else
                (do
                  if (((CRm == 0b0101#4) && ((opc2 == 0b000#3) || ((opc2 == 0b001#3) || ((opc2 == 0b100#3) || (opc2 == 0b101#3))))) : Bool)
                  then
                    (do
                      let w__20 ← (( do (__UNKNOWN_bits 32) ) : SailME Unit (BitVec 32) )
                      (R_set t w__20))
                  else
                    (do
                      (R_set t (Zeros (n := 32))))))
          SailME.throw (() : Unit)))
  else (pure (()))
  sailThrow ((Error_Undefined ()))


/-- Type quantifiers: cp_num : Int, t : Int, t2 : Int -/
def AArch32_SysRegRead64 (cp_num : Int) (instr : (BitVec 32)) (t : Int) (t2 : Int) : SailM Unit := do
  let el ← (( do (undefined_bitvector_at (← occLabel 2903) 2) ) : SailM (BitVec 2) )
  let n ← (( do (undefined_int_at (← occLabel 2904) ()) ) : SailM Int )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let (_, __tup_1) ← (( do (ELFromM32 w__0.M) ) : SailM (Bool × (BitVec 2)) )
  let el : (BitVec 2) := __tup_1
  let opc1 : (BitVec 4) := (BitVec.slice instr 4 4)
  let CRm : (BitVec 4) := (BitVec.slice instr 0 4)
  if ((((cp_num == 15) && (let b__0 := (Sail.BitVec.extractLsb CRm 3 1)
         (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 2 2)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                  b__0 0 0)) == (0#1 : (BitVec 1)))) : Bool)
         then true
         else false : Bool))) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc1 3)])) == 0#1)) : Bool)
  then
    (do
      let n : Int :=
        (BitVec.toNat
          ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access CRm 0)])) +++ (Sail.BitVec.extractLsb
              opc1 2 0)))
      if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb CRm 3 1)) == 0b000#3) : Bool)
      then
        (do
          let w__1 ← (( do (AMCGCR_read ()) ) : SailM (BitVec 32) )
          if ((n ≥b (BitVec.toNat (_get_AMCGCR_Type_CG0NC w__1))) : Bool)
          then sailThrow ((Error_Undefined ()))
          else (pure (())))
      else
        (do
          if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb CRm 3 1)) == 0b010#3) : Bool)
          then
            (do
              let w__2 ← (( do (AMCGCR_read ()) ) : SailM (BitVec 32) )
              if ((n ≥b (BitVec.toNat (_get_AMCGCR_Type_CG1NC w__2))) : Bool)
              then sailThrow ((Error_Undefined ()))
              else (pure (())))
          else (pure (()))))
  else (pure (()))
  (AArch32_AutoGen_SysRegRead64 el (integer_subrange cp_num 3 0) opc1 CRm t t2)


/-- Type quantifiers: cp_num : Int, t : Int, t2 : Int -/
def AArch32_SysRegWrite64 (cp_num : Int) (instr : (BitVec 32)) (t : Int) (t2 : Int) : SailM Unit := do
  let el ← (( do (undefined_bitvector_at (← occLabel 2906) 2) ) : SailM (BitVec 2) )
  let n ← (( do (undefined_int_at (← occLabel 2907) ()) ) : SailM Int )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let (_, __tup_1) ← (( do (ELFromM32 w__0.M) ) : SailM (Bool × (BitVec 2)) )
  let el : (BitVec 2) := __tup_1
  let opc1 : (BitVec 4) := (BitVec.slice instr 4 4)
  let CRm : (BitVec 4) := (BitVec.slice instr 0 4)
  if ((((cp_num == 15) && (let b__0 := (Sail.BitVec.extractLsb CRm 3 1)
         (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 2 2)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                  b__0 0 0)) == (0#1 : (BitVec 1)))) : Bool)
         then true
         else false : Bool))) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc1 3)])) == 0#1)) : Bool)
  then
    (do
      let n : Int :=
        (BitVec.toNat
          ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access CRm 0)])) +++ (Sail.BitVec.extractLsb
              opc1 2 0)))
      if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb CRm 3 1)) == 0b000#3) : Bool)
      then
        (do
          let w__1 ← (( do (AMCGCR_read ()) ) : SailM (BitVec 32) )
          if ((n ≥b (BitVec.toNat (_get_AMCGCR_Type_CG0NC w__1))) : Bool)
          then sailThrow ((Error_Undefined ()))
          else (pure (())))
      else
        (do
          if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb CRm 3 1)) == 0b010#3) : Bool)
          then
            (do
              let w__2 ← (( do (AMCGCR_read ()) ) : SailM (BitVec 32) )
              if ((n ≥b (BitVec.toNat (_get_AMCGCR_Type_CG1NC w__2))) : Bool)
              then sailThrow ((Error_Undefined ()))
              else (pure (())))
          else (pure (()))))
  else (pure (()))
  (AArch32_AutoGen_SysRegWrite64 el (integer_subrange cp_num 3 0) opc1 CRm t t2)


def execute_aarch32_instrs_BKPT_Op_A_txt (imm16 : (BitVec 16)) : SailM Unit := do
  (AArch32_SoftwareBreakpoint imm16)


def decode_aarch32_instrs_WFE_A1enc_A_txt (cond : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:40507.29-40507.30"
      (execute_aarch32_instrs_WFE_Op_A_txt ()))
  else (pure (()))


def decode_aarch32_instrs_WFE_T1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (execute_aarch32_instrs_WFE_Op_A_txt ()))
  else (pure (()))


def decode_aarch32_instrs_WFE_T2enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (execute_aarch32_instrs_WFE_Op_A_txt ()))
  else (pure (()))


def decode_aarch32_instrs_WFI_A1enc_A_txt (cond : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:40578.29-40578.30"
      (execute_aarch32_instrs_WFI_Op_A_txt ()))
  else (pure (()))


def decode_aarch32_instrs_WFI_T1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (execute_aarch32_instrs_WFI_Op_A_txt ()))
  else (pure (()))


def decode_aarch32_instrs_WFI_T2enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (execute_aarch32_instrs_WFI_Op_A_txt ()))
  else (pure (()))


def execute_aarch32_instrs_ESB_Op_A_txt (_ : Unit) : SailM Unit := do
  let _ : Unit := (SynchronizeErrors ())
  (AArch32_ESBOperation ())
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__0.EL == EL0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL1) : Bool))))) : Bool)
    then
      (do
        (EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      (AArch32_vESBOperation ()))
  else (pure (()))
  (TakeUnmaskedSErrorInterrupts ())


/-- Type quantifiers: d : Nat, k_decrypt : Bool, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_aes_round (d : Nat) (decrypt : Bool) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let operand1 ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let operand2 ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let result : (BitVec 128) := (operand1 ^^^ operand2)
  let result ← (( do
    if (decrypt : Bool)
    then
      (do
        (AESInvSubBytes (AESInvShiftRows result)))
    else
      (do
        (AESSubBytes (AESShiftRows result))) ) : SailM (BitVec 128) )
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, k_decrypt : Bool, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_aes_mix (d : Nat) (decrypt : Bool) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let operand ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3942) 128) ) : SailM (BitVec 128) )
  let result ← (( do
    if (decrypt : Bool)
    then
      (do
        (AESInvMixColumns operand))
    else
      (do
        (AESMixColumns operand)) ) : SailM (BitVec 128) )
  (V_set d 128 result)


def decode_autda_aarch64_instrs_integer_pac_autda_dp_1src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) : SailM Unit := do
  let source_is_sp : Bool := false
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let source_is_sp ← (( do
    if ((Z == 0#1) : Bool)
    then
      (let source_is_sp : Bool :=
        if ((n == 31) : Bool)
        then true
        else source_is_sp
      (pure (source_is_sp)))
    else
      (do
        if ((n != 31) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (source_is_sp))) ) : SailM Bool )
  (execute_aarch64_instrs_integer_pac_autda_dp_1src (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) source_is_sp)


def decode_autdb_aarch64_instrs_integer_pac_autdb_dp_1src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) : SailM Unit := do
  let source_is_sp : Bool := false
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let source_is_sp ← (( do
    if ((Z == 0#1) : Bool)
    then
      (let source_is_sp : Bool :=
        if ((n == 31) : Bool)
        then true
        else source_is_sp
      (pure (source_is_sp)))
    else
      (do
        if ((n != 31) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (source_is_sp))) ) : SailM Bool )
  (execute_aarch64_instrs_integer_pac_autdb_dp_1src (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) source_is_sp)


def decode_autia_aarch64_instrs_integer_pac_autia_dp_1src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) : SailM Unit := do
  let source_is_sp : Bool := false
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let source_is_sp ← (( do
    if ((Z == 0#1) : Bool)
    then
      (let source_is_sp : Bool :=
        if ((n == 31) : Bool)
        then true
        else source_is_sp
      (pure (source_is_sp)))
    else
      (do
        if ((n != 31) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (source_is_sp))) ) : SailM Bool )
  (execute_aarch64_instrs_integer_pac_autia_dp_1src (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) source_is_sp)


def decode_autia_aarch64_instrs_integer_pac_autia_hint (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let d : Int := 17
  let n : Int := 0
  let source_is_sp : Bool := false
  let (d, n, source_is_sp) ← (( do
    match (BitVec.setWidth 7 (CRm +++ op2)) with
    | 0b0011100 =>
      (let d : Int := 30
      let n : Int := 31
      (pure ((d, n, source_is_sp))))
    | 0b0011101 =>
      (let d : Int := 30
      let source_is_sp : Bool := true
      (pure ((d, n, source_is_sp))))
    | 0b0001100 =>
      (let d : Int := 17
      let n : Int := 16
      (pure ((d, n, source_is_sp))))
    | 0b0001000 => sailThrow ((Error_See "PACIA"))
    | 0b0001010 => sailThrow ((Error_See "PACIB"))
    | 0b0001110 => sailThrow ((Error_See "AUTIB"))
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
                if (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb b__0 6 1)) == (0b001111#6 : (BitVec 6))) : Bool)
                then sailThrow ((Error_See "AUTIB"))
                else
                  (do
                    match b__0 with
                    | 0b0000111 => sailThrow ((Error_See "XPACLRI"))
                    | _ => sailThrow ((Error_See "HINT")))))
        (pure ((d, n, source_is_sp)))) ) : SailM (Int × Int × Bool) )
  let n : Int := n
  let d : Int := d
  ArmFull.assert ((0 ≤b n) && (n ≤b 31)) "/home/doug/boss-scratch/armcert-defects/c27-accepted/armcert_c27.sail:141.43-141.44"
  (execute_aarch64_instrs_integer_pac_autia_dp_1src (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) source_is_sp)


def decode_autib_aarch64_instrs_integer_pac_autib_dp_1src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) : SailM Unit := do
  let source_is_sp : Bool := false
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let source_is_sp ← (( do
    if ((Z == 0#1) : Bool)
    then
      (let source_is_sp : Bool :=
        if ((n == 31) : Bool)
        then true
        else source_is_sp
      (pure (source_is_sp)))
    else
      (do
        if ((n != 31) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (source_is_sp))) ) : SailM Bool )
  (execute_aarch64_instrs_integer_pac_autib_dp_1src (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) source_is_sp)


end ArmFull.Functions
