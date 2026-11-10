import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0036
import ArmFull.Fn.M0038
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0046
import ArmFull.Fn.M0087
import ArmFull.Fn.M0100
import ArmFull.Fn.M0124
import ArmFull.Fn.M0144
import ArmFull.Fn.M0151
import ArmFull.Fn.M0154
import ArmFull.Fn.M0175
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
import ArmFull.Fn.M0186
import ArmFull.Fn.M0196
import ArmFull.Fn.M0227
import ArmFull.Fn.M0228
import ArmFull.Fn.M0229
import ArmFull.Fn.M0230
import ArmFull.Fn.M0231
import ArmFull.Fn.M0232
import ArmFull.Fn.M0233
import ArmFull.Fn.M0234
import ArmFull.Fn.M0235
import ArmFull.Fn.M0236

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

def AArch32_ResetSIMDFPRegisters (_ : Unit) : SailM Unit := do
  let loop_i_lower : Nat := 0
  let loop_i_upper : Nat := 15
  (do
    let mut loop_vars := ()
    for i in [loop_i_lower:loop_i_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do (__UNKNOWN_bits 128) ) : SailM (BitVec 128) )
        (Q_set i w__0)
    (pure loop_vars))


def decode_aarch32_instrs_PLD_l_A1enc_A_txt (U : (BitVec 1)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      (execute_aarch32_instrs_PLD_l_Op_A_txt add imm32))
  else (pure (()))


def decode_aarch32_instrs_PLD_l_T1enc_A_txt (U : (BitVec 1)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      (execute_aarch32_instrs_PLD_l_Op_A_txt add imm32))
  else (pure (()))


def decode_aarch32_instrs_PLI_i_A1enc_A_txt (U : (BitVec 1)) (Rn : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      (execute_aarch32_instrs_PLI_i_Op_A_txt add imm32 (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_PLI_i_T1enc_A_txt (Rn : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "encoding T3"))
      else (pure (()))
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := true
      (execute_aarch32_instrs_PLI_i_Op_A_txt add imm32 (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_PLI_i_T2enc_A_txt (Rn : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "encoding T3"))
      else (pure (()))
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      let add : Bool := false
      (execute_aarch32_instrs_PLI_i_Op_A_txt add imm32 (Sail.Int.toNatChecked (n))))
  else (pure (()))


def decode_aarch32_instrs_PLI_i_T3enc_A_txt (U : (BitVec 1)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let n : Nat := 15
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      (execute_aarch32_instrs_PLI_i_Op_A_txt add imm32 n))
  else (pure (()))


def decode_aarch32_instrs_SETEND_A1enc_A_txt (E : (BitVec 1)) : SailM Unit := do
  let set_bigend : Bool := (E == 1#1)
  (execute_aarch32_instrs_SETEND_Op_A_txt set_bigend)


def decode_aarch32_instrs_SETEND_T1enc_A_txt (E : (BitVec 1)) : SailM Unit := do
  let set_bigend : Bool := (E == 1#1)
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  (execute_aarch32_instrs_SETEND_Op_A_txt set_bigend)


def execute_aarch32_instrs_DCPS1_Op_A_txt (_ : Unit) : SailM Unit := do
  let LR_svc ← (( do (undefined_bitvector_at (← occLabel 3793) 32) ) : SailM (BitVec 32) )
  let tge ← (( do (undefined_bitvector_at (← occLabel 3794) 1) ) : SailM (BitVec 1) )
  let w__0 ← (( do (Halted ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__3 ← (( do
    if ((← do
         (EL2Enabled ())) : Bool)
    then
      (do
        let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__2.EL == EL0) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__3 : Bool)
  then
    (do
      let w__4 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
      let tge ← (( do
        if (w__4 : Bool)
        then
          (do
            let w__5 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
            (pure ((_get_HCR_Type_TGE w__5))))
        else
          (do
            let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((_get_HCR_EL2_Type_TGE w__6)))) ) : SailM (BitVec 1) )
      if ((tge == 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (())))
  else (pure (()))
  let w__9 ← (( do
    if ((← do
         let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__7.EL != EL0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        (ELUsingAArch32 EL1)) ) : SailM Bool )
  if (w__9 : Bool)
  then
    (do
      let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__10.M == M32_Monitor) : Bool)
      then
        (do
          let w__11 ← (( do readReg SCR ) : SailM (BitVec 32) )
          writeReg SCR (Sail.BitVec.updateSubrange w__11 0 0 0#1))
      else (pure (()))
      let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__12.EL != EL2) : Bool)
      then
        (do
          (AArch32_WriteMode M32_Svc)
          let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__14 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
          writeReg PSTATE { w__13 with E := (_get_SCTLR_Type_EE w__14) }
          let w__17 ← (( do
            if ((← do
                 (HavePANExt ())) : Bool)
            then
              (do
                let w__16 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
                (pure ((((_get_SCTLR_Type_SPAN w__16) == 0#1) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__17 : Bool)
          then
            (do
              let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__18 with PAN := 1#1 })
          else (pure (()))
          let w__19 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
          let LR_svc := (w__19 : (BitVec 32))
          let w__20 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
          (SPSR_svc_write (Mk_SPSR_svc_Type w__20)))
      else
        (do
          let w__21 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__22 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
          writeReg PSTATE { w__21 with E := (_get_HSCTLR_Type_EE w__22) }
          let w__23 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
          (ELR_hyp_write w__23)
          let w__24 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
          (HSR_write (Mk_HSR_Type w__24))
          let w__25 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
          (SPSR_hyp_write (Mk_SPSR_hyp_Type w__25)))
      let w__26 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      (DLR_write w__26)
      let w__27 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      (DSPSR_write (Mk_DSPSR_Type w__27)))
  else
    (do
      (AArch64_MaybeZeroRegisterUppers ())
      (MaybeZeroSVEUppers EL1)
      let w__28 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__28 with nRW := 0#1 }
      let w__29 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__29 with SP := 1#1 }
      let w__30 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__30 with EL := EL1 }
      let w__33 ← (( do
        if ((← do
             (HavePANExt ())) : Bool)
        then
          (do
            let w__32 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            (pure ((((_get_SCTLR_EL1_Type_SPAN w__32) == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__33 : Bool)
      then
        (do
          let w__34 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__34 with PAN := 1#1 })
      else (pure (()))
      let w__35 ← (( do (HaveUAOExt ()) ) : SailM Bool )
      if (w__35 : Bool)
      then
        (do
          let w__36 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__36 with UAO := 0#1 })
      else (pure (()))
      let w__37 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg ELR_EL1 w__37
      let w__38 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg ESR_EL1 (Mk_ESR_EL1_Type w__38)
      let w__39 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg SPSR_EL1 (Mk_SPSR_EL1_Type w__39)
      let w__40 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg DLR_EL0 w__40
      let w__41 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg DSPSR_EL0 (Mk_DSPSR_EL0_Type w__41)
      let w__46 ← (( do
        if ((← do
             if ((← do
                  (HaveIESB ())) : Bool)
             then
               (do
                 let w__43 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
                 (pure ((((_get_SCTLR_EL1_Type_IESB w__43) == 1#1) : Bool))))
             else (pure false)) : Bool)
        then
          (do
            let w__45 ← (( do (ConstrainUnpredictableBool Unpredictable_IESBinDebug) ) : SailM
              Bool )
            (pure (((! w__45) : Bool))))
        else (pure false) ) : SailM Bool )
      let _ : Unit :=
        if (w__46 : Bool)
        then (SynchronizeErrors ())
        else ()
      (pure (())))
  (UpdateEDSCRFields ())


def execute_aarch32_instrs_DCPS2_Op_A_txt (_ : Unit) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (Halted ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (EL2Enabled ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__3 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
  if (w__3 : Bool)
  then
    (do
      (AArch32_WriteMode M32_Hyp)
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__5 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
      writeReg PSTATE { w__4 with E := (_get_HSCTLR_Type_EE w__5) }
      let w__6 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      (ELR_hyp_write w__6)
      let w__7 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      (HSR_write (Mk_HSR_Type w__7))
      let w__8 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      (SPSR_hyp_write (Mk_SPSR_hyp_Type w__8))
      let w__9 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      (DLR_write w__9)
      let w__10 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      (DSPSR_write (Mk_DSPSR_Type w__10)))
  else
    (do
      (AArch64_MaybeZeroRegisterUppers ())
      (MaybeZeroSVEUppers EL2)
      let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__11 with nRW := 0#1 }
      let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__12 with SP := 1#1 }
      let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__13 with EL := EL2 }
      let w__20 ← (( do
        if ((← do
             if ((← do
                  if ((← do
                       (HavePANExt ())) : Bool)
                  then
                    (do
                      let w__15 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
                      (pure ((((_get_SCTLR_EL2_Type_SPAN w__15) == 0#1) : Bool))))
                  else (pure false)) : Bool)
             then
               (do
                 let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                 (pure ((((_get_HCR_EL2_Type_E2H w__17) == 1#1) : Bool))))
             else (pure false)) : Bool)
        then
          (do
            let w__19 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_TGE w__19) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__20 : Bool)
      then
        (do
          let w__21 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__21 with PAN := 1#1 })
      else (pure (()))
      let w__22 ← (( do (HaveUAOExt ()) ) : SailM Bool )
      if (w__22 : Bool)
      then
        (do
          let w__23 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__23 with UAO := 0#1 })
      else (pure (()))
      let w__24 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg ELR_EL2 w__24
      let w__25 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg ESR_EL2 (Mk_ESR_EL2_Type w__25)
      let w__26 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg SPSR_EL2 (Mk_SPSR_EL2_Type w__26)
      let w__27 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg DLR_EL0 w__27
      let w__28 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg DSPSR_EL0 (Mk_DSPSR_EL0_Type w__28)
      let w__33 ← (( do
        if ((← do
             if ((← do
                  (HaveIESB ())) : Bool)
             then
               (do
                 let w__30 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
                 (pure ((((_get_SCTLR_EL2_Type_IESB w__30) == 1#1) : Bool))))
             else (pure false)) : Bool)
        then
          (do
            let w__32 ← (( do (ConstrainUnpredictableBool Unpredictable_IESBinDebug) ) : SailM
              Bool )
            (pure (((! w__32) : Bool))))
        else (pure false) ) : SailM Bool )
      let _ : Unit :=
        if (w__33 : Bool)
        then (SynchronizeErrors ())
        else ()
      (pure (())))
  (UpdateEDSCRFields ())


def execute_aarch32_instrs_DCPS3_Op_A_txt (_ : Unit) : SailM Unit := do
  let from_secure ← (( do (undefined_bool_at (← occLabel 3795) ()) ) : SailM Bool )
  let sync_errors ← (( do (undefined_bool_at (← occLabel 3796) ()) ) : SailM Bool )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (Halted ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
        (pure ((((_get_EDSCR_Type_SDD w__1) == 1#1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__3 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
  if (w__3 : Bool)
  then
    (do
      let w__4 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
      let from_secure : Bool := (BEq.beq w__4 SS_Secure)
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__5.M == M32_Monitor) : Bool)
      then
        (do
          let w__6 ← (( do readReg SCR ) : SailM (BitVec 32) )
          writeReg SCR (Sail.BitVec.updateSubrange w__6 0 0 0#1))
      else (pure (()))
      (AArch32_WriteMode M32_Monitor)
      let w__7 ← (( do (HavePANExt ()) ) : SailM Bool )
      if (w__7 : Bool)
      then
        (do
          if ((! from_secure) : Bool)
          then
            (do
              let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__8 with PAN := 0#1 })
          else
            (do
              let w__9 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
              if (((_get_SCTLR_Type_SPAN w__9) == 0#1) : Bool)
              then
                (do
                  let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
                  writeReg PSTATE { w__10 with PAN := 1#1 })
              else (pure (()))))
      else (pure (()))
      let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__12 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
      writeReg PSTATE { w__11 with E := (_get_SCTLR_Type_EE w__12) }
      let w__13 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      writeReg LR_mon w__13
      let w__14 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      writeReg SPSR_mon (Mk_SPSR_mon_Type w__14)
      let w__15 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      (DLR_write w__15)
      let w__16 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      (DSPSR_write (Mk_DSPSR_Type w__16)))
  else
    (do
      (AArch64_MaybeZeroRegisterUppers ())
      (MaybeZeroSVEUppers EL3)
      let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__17 with nRW := 0#1 }
      let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__18 with SP := 1#1 }
      let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__19 with EL := EL3 }
      let w__20 ← (( do (HaveUAOExt ()) ) : SailM Bool )
      if (w__20 : Bool)
      then
        (do
          let w__21 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__21 with UAO := 0#1 })
      else (pure (()))
      let w__22 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg ELR_EL3 w__22
      let w__23 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg ESR_EL3 (Mk_ESR_EL3_Type w__23)
      let w__24 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg SPSR_EL3 (Mk_SPSR_EL3_Type w__24)
      let w__25 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg DLR_EL0 w__25
      let w__26 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
      writeReg DSPSR_EL0 (Mk_DSPSR_EL0_Type w__26)
      let w__29 ← (( do
        if ((← do
             (HaveIESB ())) : Bool)
        then
          (do
            let w__28 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
            (pure ((((_get_SCTLR_EL3_Type_IESB w__28) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      let sync_errors : Bool := (w__29 : Bool)
      let w__34 ← (( do
        if ((← do
             if ((← do
                  (HaveDoubleFaultExt ())) : Bool)
             then
               (do
                 let w__31 ← (( do (EffectiveEA ()) ) : SailM (BitVec 1) )
                 (pure (((w__31 == 1#1) : Bool))))
             else (pure false)) : Bool)
        then
          (do
            let w__33 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            (pure ((((_get_SCR_EL3_Type_NMEA w__33) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      let sync_errors : Bool :=
        if (w__34 : Bool)
        then true
        else sync_errors
      let w__35 ← (( do (ConstrainUnpredictableBool Unpredictable_IESBinDebug) ) : SailM Bool )
      let sync_errors : Bool :=
        if ((! w__35) : Bool)
        then false
        else sync_errors
      let _ : Unit :=
        if (sync_errors : Bool)
        then (SynchronizeErrors ())
        else ()
      (pure (())))
  (UpdateEDSCRFields ())


def decode_addg_aarch64_instrs_integer_tags_mcaddtag (Xd : (BitVec 5)) (Xn : (BitVec 5)) (uimm4 : (BitVec 4)) (op3 : (BitVec 2)) (uimm6 : (BitVec 6)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Xd)
  let n : Int := (BitVec.toNat Xn)
  let tag_offset : (BitVec 4) := uimm4
  let offset : (BitVec 64) := ((Sail.BitVec.zeroExtend uimm6 64) <<< LOG2_TAG_GRANULE)
  let ADD : Bool := true
  (execute_aarch64_instrs_integer_tags_mcaddtag ADD (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) offset tag_offset)


def decode_irg_aarch64_instrs_integer_tags_mcinsertrandomtag (Xd : (BitVec 5)) (Xn : (BitVec 5)) (Xm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Xd)
  let n : Int := (BitVec.toNat Xn)
  let m : Int := (BitVec.toNat Xm)
  (execute_aarch64_instrs_integer_tags_mcinsertrandomtag (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_subg_aarch64_instrs_integer_tags_mcsubtag (Xd : (BitVec 5)) (Xn : (BitVec 5)) (uimm4 : (BitVec 4)) (op3 : (BitVec 2)) (uimm6 : (BitVec 6)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Xd)
  let n : Int := (BitVec.toNat Xn)
  let tag_offset : (BitVec 4) := uimm4
  let offset : (BitVec 64) := ((Sail.BitVec.zeroExtend uimm6 64) <<< LOG2_TAG_GRANULE)
  let ADD : Bool := false
  (execute_aarch64_instrs_integer_tags_mcsubtag ADD (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) offset tag_offset)


/-- Type quantifiers: pc : Int -/
def __DecodeA32_Media (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  let w__2 ← (( do
    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode 27 21)) == (0b0111110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
             __opcode 6 0)) == (0b0011111#7 : (BitVec 7)))) : Bool) : Bool)
    then
      (do
        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
        then
          (do
            let w__0 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__0 <b 2856) : Bool))))
        else (pure false))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      writeReg SEE 2856
      let cond := (BitVec.slice __opcode 28 4)
      let msb := (BitVec.slice __opcode 16 5)
      let Rd := (BitVec.slice __opcode 12 4)
      let lsb := (BitVec.slice __opcode 7 5)
      (decode_aarch32_instrs_BFC_A1enc_A_txt cond msb Rd lsb))
  else
    (do
      let w__5 ← (( do
        if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb __opcode 27 21)) == (0b0111110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                 __opcode 6 4)) == (0b001#3 : (BitVec 3)))) : Bool) : Bool)
        then
          (do
            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
            then
              (do
                let w__3 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__3 <b 2858) : Bool))))
            else (pure false))
        else (pure false) ) : SailM Bool )
      if (w__5 : Bool)
      then
        (do
          writeReg SEE 2858
          let cond := (BitVec.slice __opcode 28 4)
          let msb := (BitVec.slice __opcode 16 5)
          let Rd := (BitVec.slice __opcode 12 4)
          let lsb := (BitVec.slice __opcode 7 5)
          let Rn := (BitVec.slice __opcode 0 4)
          (decode_aarch32_instrs_BFI_A1enc_A_txt cond msb Rd lsb Rn))
      else
        (do
          let w__8 ← (( do
            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 27 20)) == (0x68#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                     __opcode 5 4)) == (0b01#2 : (BitVec 2)))) : Bool) : Bool)
            then
              (do
                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                then
                  (do
                    let w__6 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__6 <b 3047) : Bool))))
                else (pure false))
            else (pure false) ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              writeReg SEE 3047
              let cond := (BitVec.slice __opcode 28 4)
              let Rn := (BitVec.slice __opcode 16 4)
              let Rd := (BitVec.slice __opcode 12 4)
              let imm5 := (BitVec.slice __opcode 7 5)
              let tb := (BitVec.slice __opcode 6 1)
              let Rm := (BitVec.slice __opcode 0 4)
              (decode_aarch32_instrs_PKH_A1enc_A_txt cond Rn Rd imm5 tb Rm))
          else
            (do
              let w__11 ← (( do
                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 27 20)) == (0x62#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                         __opcode 11 4)) == (0xF1#8 : (BitVec 8)))) : Bool) : Bool)
                then
                  (do
                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                    then
                      (do
                        let w__9 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__9 <b 3064) : Bool))))
                    else (pure false))
                else (pure false) ) : SailM Bool )
              if (w__11 : Bool)
              then
                (do
                  writeReg SEE 3064
                  let cond := (BitVec.slice __opcode 28 4)
                  let Rn := (BitVec.slice __opcode 16 4)
                  let Rd := (BitVec.slice __opcode 12 4)
                  let Rm := (BitVec.slice __opcode 0 4)
                  if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                               __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 11)])) != 1#1)) : Bool)
                  then sailThrow ((Error_ConstrainedUnpredictable ()))
                  else
                    (do
                      (decode_aarch32_instrs_QADD16_A1enc_A_txt cond Rn Rd Rm)))
              else
                (do
                  let w__14 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 27 20)) == (0x62#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                             __opcode 11 4)) == (0xF9#8 : (BitVec 8)))) : Bool) : Bool)
                    then
                      (do
                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                        then
                          (do
                            let w__12 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__12 <b 3066) : Bool))))
                        else (pure false))
                    else (pure false) ) : SailM Bool )
                  if (w__14 : Bool)
                  then
                    (do
                      writeReg SEE 3066
                      let cond := (BitVec.slice __opcode 28 4)
                      let Rn := (BitVec.slice __opcode 16 4)
                      let Rd := (BitVec.slice __opcode 12 4)
                      let Rm := (BitVec.slice __opcode 0 4)
                      if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                   __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 11)])) != 1#1)) : Bool)
                      then sailThrow ((Error_ConstrainedUnpredictable ()))
                      else
                        (do
                          (decode_aarch32_instrs_QADD8_A1enc_A_txt cond Rn Rd Rm)))
                  else
                    (do
                      let w__17 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 27
                                 20)) == (0x62#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                 __opcode 11 4)) == (0xF3#8 : (BitVec 8)))) : Bool) : Bool)
                        then
                          (do
                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                            then
                              (do
                                let w__15 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__15 <b 3070) : Bool))))
                            else (pure false))
                        else (pure false) ) : SailM Bool )
                      if (w__17 : Bool)
                      then
                        (do
                          writeReg SEE 3070
                          let cond := (BitVec.slice __opcode 28 4)
                          let Rn := (BitVec.slice __opcode 16 4)
                          let Rd := (BitVec.slice __opcode 12 4)
                          let Rm := (BitVec.slice __opcode 0 4)
                          if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                       __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 11)])) != 1#1)) : Bool)
                          then sailThrow ((Error_ConstrainedUnpredictable ()))
                          else
                            (do
                              (decode_aarch32_instrs_QASX_A1enc_A_txt cond Rn Rd Rm)))
                      else
                        (do
                          let w__20 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode
                                     27 20)) == (0x62#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                     __opcode 11 4)) == (0xF5#8 : (BitVec 8)))) : Bool) : Bool)
                            then
                              (do
                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                then
                                  (do
                                    let w__18 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__18 <b 3076) : Bool))))
                                else (pure false))
                            else (pure false) ) : SailM Bool )
                          if (w__20 : Bool)
                          then
                            (do
                              writeReg SEE 3076
                              let cond := (BitVec.slice __opcode 28 4)
                              let Rn := (BitVec.slice __opcode 16 4)
                              let Rd := (BitVec.slice __opcode 12 4)
                              let Rm := (BitVec.slice __opcode 0 4)
                              if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                             __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                           __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         __opcode 11)])) != 1#1)) : Bool)
                              then sailThrow ((Error_ConstrainedUnpredictable ()))
                              else
                                (do
                                  (decode_aarch32_instrs_QSAX_A1enc_A_txt cond Rn Rd Rm)))
                          else
                            (do
                              let w__23 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                         __opcode 27 20)) == (0x62#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                         __opcode 11 4)) == (0xF7#8 : (BitVec 8)))) : Bool) : Bool)
                                then
                                  (do
                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode 28
                                           4)) != 0b1111#4) : Bool) : Bool)
                                    then
                                      (do
                                        let w__21 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__21 <b 3078) : Bool))))
                                    else (pure false))
                                else (pure false) ) : SailM Bool )
                              if (w__23 : Bool)
                              then
                                (do
                                  writeReg SEE 3078
                                  let cond := (BitVec.slice __opcode 28 4)
                                  let Rn := (BitVec.slice __opcode 16 4)
                                  let Rd := (BitVec.slice __opcode 12 4)
                                  let Rm := (BitVec.slice __opcode 0 4)
                                  if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode
                                                 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                 __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                               __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                             __opcode 11)])) != 1#1)) : Bool)
                                  then sailThrow ((Error_ConstrainedUnpredictable ()))
                                  else
                                    (do
                                      (decode_aarch32_instrs_QSUB16_A1enc_A_txt cond Rn Rd Rm)))
                              else
                                (do
                                  let w__26 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                             __opcode 27 20)) == (0x62#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                             __opcode 11 4)) == (0xFF#8 : (BitVec 8)))) : Bool) : Bool)
                                    then
                                      (do
                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice __opcode
                                               28 4)) != 0b1111#4) : Bool) : Bool)
                                        then
                                          (do
                                            let w__24 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__24 <b 3080) : Bool))))
                                        else (pure false))
                                    else (pure false) ) : SailM Bool )
                                  if (w__26 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3080
                                      let cond := (BitVec.slice __opcode 28 4)
                                      let Rn := (BitVec.slice __opcode 16 4)
                                      let Rd := (BitVec.slice __opcode 12 4)
                                      let Rm := (BitVec.slice __opcode 0 4)
                                      if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                     __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                     __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                   __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                 __opcode 11)])) != 1#1)) : Bool)
                                      then sailThrow ((Error_ConstrainedUnpredictable ()))
                                      else
                                        (do
                                          (decode_aarch32_instrs_QSUB8_A1enc_A_txt cond Rn Rd Rm)))
                                  else
                                    (do
                                      let w__29 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                 __opcode 27 16)) == (0x6FF#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                 __opcode 11 4)) == (0xF3#8 : (BitVec 8)))) : Bool) : Bool)
                                        then
                                          (do
                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                   __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                            then
                                              (do
                                                let w__27 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__27 <b 3084) : Bool))))
                                            else (pure false))
                                        else (pure false) ) : SailM Bool )
                                      if (w__29 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3084
                                          let cond := (BitVec.slice __opcode 28 4)
                                          let Rd := (BitVec.slice __opcode 12 4)
                                          let Rm := (BitVec.slice __opcode 0 4)
                                          if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                           __opcode 8)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                         __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                       __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                     __opcode 11)])) != 1#1)) : Bool)
                                          then sailThrow ((Error_ConstrainedUnpredictable ()))
                                          else
                                            (do
                                              (decode_aarch32_instrs_RBIT_A1enc_A_txt cond Rd Rm)))
                                      else
                                        (do
                                          let w__32 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                     __opcode 27 16)) == (0x6BF#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                     __opcode 11 4)) == (0xFB#8 : (BitVec 8)))) : Bool) : Bool)
                                            then
                                              (do
                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                       __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__30 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__30 <b 3086) : Bool))))
                                                else (pure false))
                                            else (pure false) ) : SailM Bool )
                                          if (w__32 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3086
                                              let cond := (BitVec.slice __opcode 28 4)
                                              let Rd := (BitVec.slice __opcode 12 4)
                                              let Rm := (BitVec.slice __opcode 0 4)
                                              if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                   __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 8)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                           __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                         __opcode 11)])) != 1#1)) : Bool)
                                              then sailThrow ((Error_ConstrainedUnpredictable ()))
                                              else
                                                (do
                                                  (decode_aarch32_instrs_REV16_A1enc_A_txt cond Rd
                                                    Rm)))
                                          else
                                            (do
                                              let w__35 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                         __opcode 27 16)) == (0x6BF#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                         __opcode 11 4)) == (0xF3#8 : (BitVec 8)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                           __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__33 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__33 <b 3089) : Bool))))
                                                    else (pure false))
                                                else (pure false) ) : SailM Bool )
                                              if (w__35 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3089
                                                  let cond := (BitVec.slice __opcode 28 4)
                                                  let Rd := (BitVec.slice __opcode 12 4)
                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                  if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                       __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                   __opcode 8)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                               __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                             __opcode 11)])) != 1#1)) : Bool)
                                                  then
                                                    sailThrow ((Error_ConstrainedUnpredictable ()))
                                                  else
                                                    (do
                                                      (decode_aarch32_instrs_REV_A1enc_A_txt cond Rd
                                                        Rm)))
                                              else
                                                (do
                                                  let w__38 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                             __opcode 27 16)) == (0x6FF#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                             __opcode 11 4)) == (0xFB#8 : (BitVec 8)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                               __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__36 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__36 <b 3092) : Bool))))
                                                        else (pure false))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__38 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3092
                                                      let cond := (BitVec.slice __opcode 28 4)
                                                      let Rd := (BitVec.slice __opcode 12 4)
                                                      let Rm := (BitVec.slice __opcode 0 4)
                                                      if ((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                           __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                       __opcode 8)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                   __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                 __opcode 11)])) != 1#1)) : Bool)
                                                      then
                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                          ()))
                                                      else
                                                        (do
                                                          (decode_aarch32_instrs_REVSH_A1enc_A_txt
                                                            cond Rd Rm)))
                                                  else
                                                    (do
                                                      let w__41 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                 __opcode 27 20)) == (0x61#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                 __opcode 11 4)) == (0xF1#8 : (BitVec 8)))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                   __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__39 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__39 <b 3105) : Bool))))
                                                            else (pure false))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__41 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3105
                                                          let cond := (BitVec.slice __opcode 28 4)
                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                          let Rd := (BitVec.slice __opcode 12 4)
                                                          let Rm := (BitVec.slice __opcode 0 4)
                                                          if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                       __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                     __opcode 11)])) != 1#1)) : Bool)
                                                          then
                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                              ()))
                                                          else
                                                            (do
                                                              (decode_aarch32_instrs_SADD16_A1enc_A_txt
                                                                cond Rn Rd Rm)))
                                                      else
                                                        (do
                                                          let w__44 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                     __opcode 27 20)) == (0x61#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                     __opcode 11 4)) == (0xF9#8 : (BitVec 8)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                       __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__42 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__42 <b 3107) : Bool))))
                                                                else (pure false))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__44 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3107
                                                              let cond :=
                                                                (BitVec.slice __opcode 28 4)
                                                              let Rn := (BitVec.slice __opcode 16 4)
                                                              let Rd := (BitVec.slice __opcode 12 4)
                                                              let Rm := (BitVec.slice __opcode 0 4)
                                                              if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                           __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                         __opcode 11)])) != 1#1)) : Bool)
                                                              then
                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                  ()))
                                                              else
                                                                (do
                                                                  (decode_aarch32_instrs_SADD8_A1enc_A_txt
                                                                    cond Rn Rd Rm)))
                                                          else
                                                            (do
                                                              let w__47 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                         __opcode 27 20)) == (0x61#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                         __opcode 11 4)) == (0xF3#8 : (BitVec 8)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                           __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__45 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__45 <b 3109) : Bool))))
                                                                    else (pure false))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__47 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3109
                                                                  let cond :=
                                                                    (BitVec.slice __opcode 28 4)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let Rd :=
                                                                    (BitVec.slice __opcode 12 4)
                                                                  let Rm :=
                                                                    (BitVec.slice __opcode 0 4)
                                                                  if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                 __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                               __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                             __opcode 11)])) != 1#1)) : Bool)
                                                                  then
                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                      ()))
                                                                  else
                                                                    (do
                                                                      (decode_aarch32_instrs_SASX_A1enc_A_txt
                                                                        cond Rn Rd Rm)))
                                                              else
                                                                (do
                                                                  let w__50 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                             __opcode 27 21)) == (0b0111101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                             __opcode 6 4)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                               __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__48 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__48 <b 3119) : Bool))))
                                                                        else (pure false))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__50 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3119
                                                                      let cond :=
                                                                        (BitVec.slice __opcode 28 4)
                                                                      let widthm1 :=
                                                                        (BitVec.slice __opcode 16 5)
                                                                      let Rd :=
                                                                        (BitVec.slice __opcode 12 4)
                                                                      let lsb :=
                                                                        (BitVec.slice __opcode 7 5)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_aarch32_instrs_SBFX_A1enc_A_txt
                                                                        cond widthm1 Rd lsb Rn))
                                                                  else
                                                                    (do
                                                                      let w__53 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                 __opcode 27 20)) == (0x71#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                 __opcode 7 4)) == (0x1#4 : (BitVec 4)))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                   __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__51 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__51 <b 3121) : Bool))))
                                                                            else (pure false))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__53 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3121
                                                                          let cond :=
                                                                            (BitVec.slice __opcode
                                                                              28 4)
                                                                          let Rd :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let Ra :=
                                                                            (BitVec.slice __opcode
                                                                              12 4)
                                                                          let Rm :=
                                                                            (BitVec.slice __opcode 8
                                                                              4)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 0
                                                                              4)
                                                                          (decode_aarch32_instrs_SDIV_A1enc_A_txt
                                                                            cond Rd Ra Rm Rn))
                                                                      else
                                                                        (do
                                                                          let w__56 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                     __opcode 27 20)) == (0x68#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                     __opcode 11 4)) == (0xFB#8 : (BitVec 8)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                       __opcode 28 4)) != 0b1111#4) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__54 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__54 <b 3123) : Bool))))
                                                                                else (pure false))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__56 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3123
                                                                              let cond :=
                                                                                (BitVec.slice
                                                                                  __opcode 28 4)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let Rd :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 4)
                                                                              let Rm :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                           __opcode
                                                                                           10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                         __opcode 11)])) != 1#1)) : Bool)
                                                                              then
                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                  ()))
                                                                              else
                                                                                (do
                                                                                  (decode_aarch32_instrs_SEL_A1enc_A_txt
                                                                                    cond Rn Rd Rm)))
                                                                          else
                                                                            (do
                                                                              let w__59 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                         __opcode 27
                                                                                         20)) == (0x63#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                         __opcode 11
                                                                                         4)) == (0xF1#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                           __opcode
                                                                                           28 4)) != 0b1111#4) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__57 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__57 <b 3130) : Bool))))
                                                                                    else
                                                                                      (pure false))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__59 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3130
                                                                                  let cond :=
                                                                                    (BitVec.slice
                                                                                      __opcode 28 4)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Rd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 4)
                                                                                  let Rm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                 __opcode
                                                                                                 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                 __opcode
                                                                                                 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                               __opcode
                                                                                               10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                             __opcode
                                                                                             11)])) != 1#1)) : Bool)
                                                                                  then
                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                      ()))
                                                                                  else
                                                                                    (do
                                                                                      (decode_aarch32_instrs_SHADD16_A1enc_A_txt
                                                                                        cond Rn Rd
                                                                                        Rm)))
                                                                              else
                                                                                (do
                                                                                  let w__62 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             27 20)) == (0x63#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             11 4)) == (0xF9#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                               __opcode
                                                                                               28 4)) != 0b1111#4) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__60 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__60 <b 3132) : Bool))))
                                                                                        else
                                                                                          (pure false))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__62 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3132
                                                                                      let cond :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          28 4)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let Rd :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 4)
                                                                                      let Rm :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          4)
                                                                                      if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                     __opcode
                                                                                                     8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                     __opcode
                                                                                                     9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                   __opcode
                                                                                                   10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                 __opcode
                                                                                                 11)])) != 1#1)) : Bool)
                                                                                      then
                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                          ()))
                                                                                      else
                                                                                        (do
                                                                                          (decode_aarch32_instrs_SHADD8_A1enc_A_txt
                                                                                            cond Rn
                                                                                            Rd Rm)))
                                                                                  else
                                                                                    (do
                                                                                      let w__65 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 27
                                                                                                 20)) == (0x63#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 11
                                                                                                 4)) == (0xF3#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                   __opcode
                                                                                                   28
                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__63 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__63 <b 3134) : Bool))))
                                                                                            else
                                                                                              (pure false))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__65 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3134
                                                                                          let cond :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              28 4)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Rd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 4)
                                                                                          let Rm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 4)
                                                                                          if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                       __opcode
                                                                                                       10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                     __opcode
                                                                                                     11)])) != 1#1)) : Bool)
                                                                                          then
                                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                                              ()))
                                                                                          else
                                                                                            (do
                                                                                              (decode_aarch32_instrs_SHASX_A1enc_A_txt
                                                                                                cond
                                                                                                Rn
                                                                                                Rd
                                                                                                Rm)))
                                                                                      else
                                                                                        (do
                                                                                          let w__68 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     27
                                                                                                     20)) == (0x63#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     11
                                                                                                     4)) == (0xF5#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                       __opcode
                                                                                                       28
                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__66 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__66 <b 3136) : Bool))))
                                                                                                else
                                                                                                  (pure false))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__68 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3136
                                                                                              let cond :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  28
                                                                                                  4)
                                                                                              let Rn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  4)
                                                                                              let Rd :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  12
                                                                                                  4)
                                                                                              let Rm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  4)
                                                                                              if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                             __opcode
                                                                                                             8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                             __opcode
                                                                                                             9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                           __opcode
                                                                                                           10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                         __opcode
                                                                                                         11)])) != 1#1)) : Bool)
                                                                                              then
                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                  ()))
                                                                                              else
                                                                                                (do
                                                                                                  (decode_aarch32_instrs_SHSAX_A1enc_A_txt
                                                                                                    cond
                                                                                                    Rn
                                                                                                    Rd
                                                                                                    Rm)))
                                                                                          else
                                                                                            (do
                                                                                              let w__71 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         27
                                                                                                         20)) == (0x63#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         11
                                                                                                         4)) == (0xF7#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                           __opcode
                                                                                                           28
                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__69 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__69 <b 3138) : Bool))))
                                                                                                    else
                                                                                                      (pure false))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__71 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3138
                                                                                                  let cond :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      28
                                                                                                      4)
                                                                                                  let Rn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      4)
                                                                                                  let Rd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      12
                                                                                                      4)
                                                                                                  let Rm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      4)
                                                                                                  if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                 __opcode
                                                                                                                 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                 __opcode
                                                                                                                 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                               __opcode
                                                                                                               10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                             __opcode
                                                                                                             11)])) != 1#1)) : Bool)
                                                                                                  then
                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                      ()))
                                                                                                  else
                                                                                                    (do
                                                                                                      (decode_aarch32_instrs_SHSUB16_A1enc_A_txt
                                                                                                        cond
                                                                                                        Rn
                                                                                                        Rd
                                                                                                        Rm)))
                                                                                              else
                                                                                                (do
                                                                                                  let w__74 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             27
                                                                                                             20)) == (0x63#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             11
                                                                                                             4)) == (0xFF#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                               __opcode
                                                                                                               28
                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__72 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__72 <b 3140) : Bool))))
                                                                                                        else
                                                                                                          (pure false))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__74 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 3140
                                                                                                      let cond :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          28
                                                                                                          4)
                                                                                                      let Rn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          4)
                                                                                                      let Rd :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          12
                                                                                                          4)
                                                                                                      let Rm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          4)
                                                                                                      if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                     __opcode
                                                                                                                     8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                     __opcode
                                                                                                                     9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                   __opcode
                                                                                                                   10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                 __opcode
                                                                                                                 11)])) != 1#1)) : Bool)
                                                                                                      then
                                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                                          ()))
                                                                                                      else
                                                                                                        (do
                                                                                                          (decode_aarch32_instrs_SHSUB8_A1enc_A_txt
                                                                                                            cond
                                                                                                            Rn
                                                                                                            Rd
                                                                                                            Rm)))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__77 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 27
                                                                                                                 20)) == (0x70#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   7
                                                                                                                   6)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   4
                                                                                                                   4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                   __opcode
                                                                                                                   28
                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__75 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__75 <b 3144) : Bool))))
                                                                                                            else
                                                                                                              (pure false))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__77 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 3144
                                                                                                          let cond :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              28
                                                                                                              4)
                                                                                                          let Rd :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              4)
                                                                                                          let Ra :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              12
                                                                                                              4)
                                                                                                          let Rm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              8
                                                                                                              4)
                                                                                                          let M :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              1)
                                                                                                          let Rn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              4)
                                                                                                          (decode_aarch32_instrs_SMLAD_A1enc_A_txt
                                                                                                            cond
                                                                                                            Rd
                                                                                                            Ra
                                                                                                            Rm
                                                                                                            M
                                                                                                            Rn))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__80 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     27
                                                                                                                     20)) == (0x74#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       7
                                                                                                                       6)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       4
                                                                                                                       4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                       __opcode
                                                                                                                       28
                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__78 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__78 <b 3150) : Bool))))
                                                                                                                else
                                                                                                                  (pure false))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__80 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 3150
                                                                                                              let cond :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  28
                                                                                                                  4)
                                                                                                              let RdHi :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  4)
                                                                                                              let RdLo :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  12
                                                                                                                  4)
                                                                                                              let Rm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  8
                                                                                                                  4)
                                                                                                              let M :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  1)
                                                                                                              let Rn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  4)
                                                                                                              (decode_aarch32_instrs_SMLALD_A1enc_A_txt
                                                                                                                cond
                                                                                                                RdHi
                                                                                                                RdLo
                                                                                                                Rm
                                                                                                                M
                                                                                                                Rn))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__83 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         27
                                                                                                                         20)) == (0x70#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           7
                                                                                                                           6)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           4
                                                                                                                           4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                           __opcode
                                                                                                                           28
                                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__81 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__81 <b 3154) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__83 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 3154
                                                                                                                  let cond :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      28
                                                                                                                      4)
                                                                                                                  let Rd :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      4)
                                                                                                                  let Ra :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      12
                                                                                                                      4)
                                                                                                                  let Rm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      8
                                                                                                                      4)
                                                                                                                  let M :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      5
                                                                                                                      1)
                                                                                                                  let Rn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      4)
                                                                                                                  (decode_aarch32_instrs_SMLSD_A1enc_A_txt
                                                                                                                    cond
                                                                                                                    Rd
                                                                                                                    Ra
                                                                                                                    Rm
                                                                                                                    M
                                                                                                                    Rn))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__86 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             27
                                                                                                                             20)) == (0x74#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               7
                                                                                                                               6)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               4
                                                                                                                               4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                               __opcode
                                                                                                                               28
                                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__84 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__84 <b 3156) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__86 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 3156
                                                                                                                      let cond :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          28
                                                                                                                          4)
                                                                                                                      let RdHi :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          4)
                                                                                                                      let RdLo :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          12
                                                                                                                          4)
                                                                                                                      let Rm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          8
                                                                                                                          4)
                                                                                                                      let M :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          5
                                                                                                                          1)
                                                                                                                      let Rn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          4)
                                                                                                                      (decode_aarch32_instrs_SMLSLD_A1enc_A_txt
                                                                                                                        cond
                                                                                                                        RdHi
                                                                                                                        RdLo
                                                                                                                        Rm
                                                                                                                        M
                                                                                                                        Rn))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__89 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 27
                                                                                                                                 20)) == (0x75#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   7
                                                                                                                                   6)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   4
                                                                                                                                   4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                   __opcode
                                                                                                                                   28
                                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__87 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__87 <b 3158) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__89 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 3158
                                                                                                                          let cond :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              28
                                                                                                                              4)
                                                                                                                          let Rd :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              4)
                                                                                                                          let Ra :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              12
                                                                                                                              4)
                                                                                                                          let Rm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              8
                                                                                                                              4)
                                                                                                                          let R :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              5
                                                                                                                              1)
                                                                                                                          let Rn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              4)
                                                                                                                          (decode_aarch32_instrs_SMMLA_A1enc_A_txt
                                                                                                                            cond
                                                                                                                            Rd
                                                                                                                            Ra
                                                                                                                            Rm
                                                                                                                            R
                                                                                                                            Rn))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__92 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     27
                                                                                                                                     20)) == (0x75#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       7
                                                                                                                                       6)) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       4
                                                                                                                                       4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                       __opcode
                                                                                                                                       28
                                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__90 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__90 <b 3160) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__92 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 3160
                                                                                                                              let cond :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  28
                                                                                                                                  4)
                                                                                                                              let Rd :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  4)
                                                                                                                              let Ra :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  12
                                                                                                                                  4)
                                                                                                                              let Rm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  8
                                                                                                                                  4)
                                                                                                                              let R :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  5
                                                                                                                                  1)
                                                                                                                              let Rn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  4)
                                                                                                                              (decode_aarch32_instrs_SMMLS_A1enc_A_txt
                                                                                                                                cond
                                                                                                                                Rd
                                                                                                                                Ra
                                                                                                                                Rm
                                                                                                                                R
                                                                                                                                Rn))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__95 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         27
                                                                                                                                         20)) == (0x75#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           15
                                                                                                                                           12)) == (0xF#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             7
                                                                                                                                             6)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             4
                                                                                                                                             4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                           __opcode
                                                                                                                                           28
                                                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__93 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__93 <b 3162) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__95 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 3162
                                                                                                                                  let cond :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      28
                                                                                                                                      4)
                                                                                                                                  let Rd :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      4)
                                                                                                                                  let Rm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      8
                                                                                                                                      4)
                                                                                                                                  let R :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      5
                                                                                                                                      1)
                                                                                                                                  let Rn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      4)
                                                                                                                                  (decode_aarch32_instrs_SMMUL_A1enc_A_txt
                                                                                                                                    cond
                                                                                                                                    Rd
                                                                                                                                    Rm
                                                                                                                                    R
                                                                                                                                    Rn))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__98 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             27
                                                                                                                                             20)) == (0x70#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               15
                                                                                                                                               12)) == (0xF#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 7
                                                                                                                                                 6)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 4
                                                                                                                                                 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                               __opcode
                                                                                                                                               28
                                                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__96 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__96 <b 3164) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__98 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 3164
                                                                                                                                      let cond :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          28
                                                                                                                                          4)
                                                                                                                                      let Rd :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          4)
                                                                                                                                      let Rm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          8
                                                                                                                                          4)
                                                                                                                                      let M :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          5
                                                                                                                                          1)
                                                                                                                                      let Rn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          4)
                                                                                                                                      (decode_aarch32_instrs_SMUAD_A1enc_A_txt
                                                                                                                                        cond
                                                                                                                                        Rd
                                                                                                                                        Rm
                                                                                                                                        M
                                                                                                                                        Rn))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__101 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 27
                                                                                                                                                 20)) == (0x70#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   15
                                                                                                                                                   12)) == (0xF#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     7
                                                                                                                                                     6)) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     4
                                                                                                                                                     4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                   __opcode
                                                                                                                                                   28
                                                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__99 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__99 <b 3172) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__101 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 3172
                                                                                                                                          let cond :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              28
                                                                                                                                              4)
                                                                                                                                          let Rd :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              4)
                                                                                                                                          let Rm :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              8
                                                                                                                                              4)
                                                                                                                                          let M :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              1)
                                                                                                                                          let Rn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              4)
                                                                                                                                          (decode_aarch32_instrs_SMUSD_A1enc_A_txt
                                                                                                                                            cond
                                                                                                                                            Rd
                                                                                                                                            Rm
                                                                                                                                            M
                                                                                                                                            Rn))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__104 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     27
                                                                                                                                                     20)) == (0x6A#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     11
                                                                                                                                                     4)) == (0xF3#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                       __opcode
                                                                                                                                                       28
                                                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__102 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__102 <b 3174) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__104 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 3174
                                                                                                                                              let cond :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  28
                                                                                                                                                  4)
                                                                                                                                              let sat_imm :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  4)
                                                                                                                                              let Rd :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  12
                                                                                                                                                  4)
                                                                                                                                              let Rn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  4)
                                                                                                                                              if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                             __opcode
                                                                                                                                                             8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                             __opcode
                                                                                                                                                             9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                           __opcode
                                                                                                                                                           10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                         __opcode
                                                                                                                                                         11)])) != 1#1)) : Bool)
                                                                                                                                              then
                                                                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                  ()))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  (decode_aarch32_instrs_SSAT16_A1enc_A_txt
                                                                                                                                                    cond
                                                                                                                                                    sat_imm
                                                                                                                                                    Rd
                                                                                                                                                    Rn)))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__107 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         27
                                                                                                                                                         21)) == (0b0110101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         5
                                                                                                                                                         4)) == (0b01#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                           __opcode
                                                                                                                                                           28
                                                                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__105 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__105 <b 3176) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__107 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 3176
                                                                                                                                                  let cond :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      28
                                                                                                                                                      4)
                                                                                                                                                  let sat_imm :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      16
                                                                                                                                                      5)
                                                                                                                                                  let Rd :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      12
                                                                                                                                                      4)
                                                                                                                                                  let imm5 :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      7
                                                                                                                                                      5)
                                                                                                                                                  let sh :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      6
                                                                                                                                                      1)
                                                                                                                                                  let Rn :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      4)
                                                                                                                                                  (decode_aarch32_instrs_SSAT_A1enc_A_txt
                                                                                                                                                    cond
                                                                                                                                                    sat_imm
                                                                                                                                                    Rd
                                                                                                                                                    imm5
                                                                                                                                                    sh
                                                                                                                                                    Rn))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__110 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             27
                                                                                                                                                             20)) == (0x61#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             11
                                                                                                                                                             4)) == (0xF5#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                               __opcode
                                                                                                                                                               28
                                                                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__108 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__108 <b 3178) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__110 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 3178
                                                                                                                                                      let cond :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          28
                                                                                                                                                          4)
                                                                                                                                                      let Rn :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          16
                                                                                                                                                          4)
                                                                                                                                                      let Rd :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          12
                                                                                                                                                          4)
                                                                                                                                                      let Rm :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          4)
                                                                                                                                                      if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                     __opcode
                                                                                                                                                                     8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                     __opcode
                                                                                                                                                                     9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                   __opcode
                                                                                                                                                                   10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                 __opcode
                                                                                                                                                                 11)])) != 1#1)) : Bool)
                                                                                                                                                      then
                                                                                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                          ()))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          (decode_aarch32_instrs_SSAX_A1enc_A_txt
                                                                                                                                                            cond
                                                                                                                                                            Rn
                                                                                                                                                            Rd
                                                                                                                                                            Rm)))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__113 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 27
                                                                                                                                                                 20)) == (0x61#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 11
                                                                                                                                                                 4)) == (0xF7#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                   __opcode
                                                                                                                                                                   28
                                                                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__111 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__111 <b 3180) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__113 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 3180
                                                                                                                                                          let cond :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              28
                                                                                                                                                              4)
                                                                                                                                                          let Rn :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              16
                                                                                                                                                              4)
                                                                                                                                                          let Rd :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              12
                                                                                                                                                              4)
                                                                                                                                                          let Rm :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              0
                                                                                                                                                              4)
                                                                                                                                                          if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                         __opcode
                                                                                                                                                                         8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                         __opcode
                                                                                                                                                                         9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                       __opcode
                                                                                                                                                                       10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                     __opcode
                                                                                                                                                                     11)])) != 1#1)) : Bool)
                                                                                                                                                          then
                                                                                                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                              ()))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              (decode_aarch32_instrs_SSUB16_A1enc_A_txt
                                                                                                                                                                cond
                                                                                                                                                                Rn
                                                                                                                                                                Rd
                                                                                                                                                                Rm)))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__116 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     27
                                                                                                                                                                     20)) == (0x61#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     11
                                                                                                                                                                     4)) == (0xFF#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                       __opcode
                                                                                                                                                                       28
                                                                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__114 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__114 <b 3182) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__116 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 3182
                                                                                                                                                              let cond :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  28
                                                                                                                                                                  4)
                                                                                                                                                              let Rn :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  16
                                                                                                                                                                  4)
                                                                                                                                                              let Rd :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  12
                                                                                                                                                                  4)
                                                                                                                                                              let Rm :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  0
                                                                                                                                                                  4)
                                                                                                                                                              if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                             __opcode
                                                                                                                                                                             8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                             __opcode
                                                                                                                                                                             9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                           __opcode
                                                                                                                                                                           10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                         __opcode
                                                                                                                                                                         11)])) != 1#1)) : Bool)
                                                                                                                                                              then
                                                                                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                  ()))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  (decode_aarch32_instrs_SSUB8_A1enc_A_txt
                                                                                                                                                                    cond
                                                                                                                                                                    Rn
                                                                                                                                                                    Rd
                                                                                                                                                                    Rm)))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__119 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         27
                                                                                                                                                                         20)) == (0x68#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         9
                                                                                                                                                                         4)) == (0b000111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                           __opcode
                                                                                                                                                                           28
                                                                                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__117 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__117 <b 3253) : Bool))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__119 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 3253
                                                                                                                                                                  let cond :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      28
                                                                                                                                                                      4)
                                                                                                                                                                  let Rn :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      16
                                                                                                                                                                      4)
                                                                                                                                                                  let Rd :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      12
                                                                                                                                                                      4)
                                                                                                                                                                  let rotate :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      10
                                                                                                                                                                      2)
                                                                                                                                                                  let Rm :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      0
                                                                                                                                                                      4)
                                                                                                                                                                  if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                             __opcode
                                                                                                                                                                             8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                             __opcode
                                                                                                                                                                             9)])) != 0#1)) : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                      ()))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      (decode_aarch32_instrs_SXTAB16_A1enc_A_txt
                                                                                                                                                                        cond
                                                                                                                                                                        Rn
                                                                                                                                                                        Rd
                                                                                                                                                                        rotate
                                                                                                                                                                        Rm)))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__122 ← (( do
                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             27
                                                                                                                                                                             20)) == (0x6A#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             9
                                                                                                                                                                             4)) == (0b000111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                               __opcode
                                                                                                                                                                               28
                                                                                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            let w__120 ← (( do
                                                                                                                                                                              readReg SEE
                                                                                                                                                                              )
                                                                                                                                                                              :
                                                                                                                                                                              SailM
                                                                                                                                                                              Int
                                                                                                                                                                              )
                                                                                                                                                                            (pure (((w__120 <b 3255) : Bool))))
                                                                                                                                                                        else
                                                                                                                                                                          (pure false))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false)
                                                                                                                                                                    )
                                                                                                                                                                    :
                                                                                                                                                                    SailM
                                                                                                                                                                    Bool
                                                                                                                                                                    )
                                                                                                                                                                  if (w__122 : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 3255
                                                                                                                                                                      let cond :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          28
                                                                                                                                                                          4)
                                                                                                                                                                      let Rn :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          16
                                                                                                                                                                          4)
                                                                                                                                                                      let Rd :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          12
                                                                                                                                                                          4)
                                                                                                                                                                      let rotate :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          10
                                                                                                                                                                          2)
                                                                                                                                                                      let Rm :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          0
                                                                                                                                                                          4)
                                                                                                                                                                      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 9)])) != 0#1)) : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                          ()))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          (decode_aarch32_instrs_SXTAB_A1enc_A_txt
                                                                                                                                                                            cond
                                                                                                                                                                            Rn
                                                                                                                                                                            Rd
                                                                                                                                                                            rotate
                                                                                                                                                                            Rm)))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      let w__125 ← (( do
                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 27
                                                                                                                                                                                 20)) == (0x6B#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 9
                                                                                                                                                                                 4)) == (0b000111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                   __opcode
                                                                                                                                                                                   28
                                                                                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                            then
                                                                                                                                                                              (do
                                                                                                                                                                                let w__123 ← (( do
                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                  )
                                                                                                                                                                                  :
                                                                                                                                                                                  SailM
                                                                                                                                                                                  Int
                                                                                                                                                                                  )
                                                                                                                                                                                (pure (((w__123 <b 3257) : Bool))))
                                                                                                                                                                            else
                                                                                                                                                                              (pure false))
                                                                                                                                                                        else
                                                                                                                                                                          (pure false)
                                                                                                                                                                        )
                                                                                                                                                                        :
                                                                                                                                                                        SailM
                                                                                                                                                                        Bool
                                                                                                                                                                        )
                                                                                                                                                                      if (w__125 : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 3257
                                                                                                                                                                          let cond :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              28
                                                                                                                                                                              4)
                                                                                                                                                                          let Rn :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              16
                                                                                                                                                                              4)
                                                                                                                                                                          let Rd :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              12
                                                                                                                                                                              4)
                                                                                                                                                                          let rotate :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              10
                                                                                                                                                                              2)
                                                                                                                                                                          let Rm :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              0
                                                                                                                                                                              4)
                                                                                                                                                                          if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     9)])) != 0#1)) : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                              ()))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              (decode_aarch32_instrs_SXTAH_A1enc_A_txt
                                                                                                                                                                                cond
                                                                                                                                                                                Rn
                                                                                                                                                                                Rd
                                                                                                                                                                                rotate
                                                                                                                                                                                Rm)))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          let w__128 ← (( do
                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     27
                                                                                                                                                                                     16)) == (0x68F#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     9
                                                                                                                                                                                     4)) == (0b000111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                            then
                                                                                                                                                                              (do
                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                       __opcode
                                                                                                                                                                                       28
                                                                                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                then
                                                                                                                                                                                  (do
                                                                                                                                                                                    let w__126 ← (( do
                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                      )
                                                                                                                                                                                      :
                                                                                                                                                                                      SailM
                                                                                                                                                                                      Int
                                                                                                                                                                                      )
                                                                                                                                                                                    (pure (((w__126 <b 3259) : Bool))))
                                                                                                                                                                                else
                                                                                                                                                                                  (pure false))
                                                                                                                                                                            else
                                                                                                                                                                              (pure false)
                                                                                                                                                                            )
                                                                                                                                                                            :
                                                                                                                                                                            SailM
                                                                                                                                                                            Bool
                                                                                                                                                                            )
                                                                                                                                                                          if (w__128 : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              writeReg SEE 3259
                                                                                                                                                                              let cond :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  28
                                                                                                                                                                                  4)
                                                                                                                                                                              let Rd :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  12
                                                                                                                                                                                  4)
                                                                                                                                                                              let rotate :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  10
                                                                                                                                                                                  2)
                                                                                                                                                                              let Rm :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  0
                                                                                                                                                                                  4)
                                                                                                                                                                              if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         9)])) != 0#1)) : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                  ()))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  (decode_aarch32_instrs_SXTB16_A1enc_A_txt
                                                                                                                                                                                    cond
                                                                                                                                                                                    Rd
                                                                                                                                                                                    rotate
                                                                                                                                                                                    Rm)))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              let w__131 ← (( do
                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         27
                                                                                                                                                                                         16)) == (0x6AF#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         9
                                                                                                                                                                                         4)) == (0b000111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                                then
                                                                                                                                                                                  (do
                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                           __opcode
                                                                                                                                                                                           28
                                                                                                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                    then
                                                                                                                                                                                      (do
                                                                                                                                                                                        let w__129 ← (( do
                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                          )
                                                                                                                                                                                          :
                                                                                                                                                                                          SailM
                                                                                                                                                                                          Int
                                                                                                                                                                                          )
                                                                                                                                                                                        (pure (((w__129 <b 3261) : Bool))))
                                                                                                                                                                                    else
                                                                                                                                                                                      (pure false))
                                                                                                                                                                                else
                                                                                                                                                                                  (pure false)
                                                                                                                                                                                )
                                                                                                                                                                                :
                                                                                                                                                                                SailM
                                                                                                                                                                                Bool
                                                                                                                                                                                )
                                                                                                                                                                              if (w__131 : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  writeReg SEE 3261
                                                                                                                                                                                  let cond :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      28
                                                                                                                                                                                      4)
                                                                                                                                                                                  let Rd :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      12
                                                                                                                                                                                      4)
                                                                                                                                                                                  let rotate :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      10
                                                                                                                                                                                      2)
                                                                                                                                                                                  let Rm :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      0
                                                                                                                                                                                      4)
                                                                                                                                                                                  if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             9)])) != 0#1)) : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                      ()))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      (decode_aarch32_instrs_SXTB_A1enc_A_txt
                                                                                                                                                                                        cond
                                                                                                                                                                                        Rd
                                                                                                                                                                                        rotate
                                                                                                                                                                                        Rm)))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  let w__134 ← (( do
                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             27
                                                                                                                                                                                             16)) == (0x6BF#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             9
                                                                                                                                                                                             4)) == (0b000111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                                    then
                                                                                                                                                                                      (do
                                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                               __opcode
                                                                                                                                                                                               28
                                                                                                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                        then
                                                                                                                                                                                          (do
                                                                                                                                                                                            let w__132 ← (( do
                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                              )
                                                                                                                                                                                              :
                                                                                                                                                                                              SailM
                                                                                                                                                                                              Int
                                                                                                                                                                                              )
                                                                                                                                                                                            (pure (((w__132 <b 3264) : Bool))))
                                                                                                                                                                                        else
                                                                                                                                                                                          (pure false))
                                                                                                                                                                                    else
                                                                                                                                                                                      (pure false)
                                                                                                                                                                                    )
                                                                                                                                                                                    :
                                                                                                                                                                                    SailM
                                                                                                                                                                                    Bool
                                                                                                                                                                                    )
                                                                                                                                                                                  if (w__134 : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (do
                                                                                                                                                                                      writeReg SEE 3264
                                                                                                                                                                                      let cond :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          28
                                                                                                                                                                                          4)
                                                                                                                                                                                      let Rd :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          12
                                                                                                                                                                                          4)
                                                                                                                                                                                      let rotate :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          10
                                                                                                                                                                                          2)
                                                                                                                                                                                      let Rm :=
                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                          __opcode
                                                                                                                                                                                          0
                                                                                                                                                                                          4)
                                                                                                                                                                                      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                 8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                 9)])) != 0#1)) : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                          ()))
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          (decode_aarch32_instrs_SXTH_A1enc_A_txt
                                                                                                                                                                                            cond
                                                                                                                                                                                            Rd
                                                                                                                                                                                            rotate
                                                                                                                                                                                            Rm)))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      let w__137 ← (( do
                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                 27
                                                                                                                                                                                                 20)) == (0x65#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                 11
                                                                                                                                                                                                 4)) == (0xF1#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                                                        then
                                                                                                                                                                                          (do
                                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                   28
                                                                                                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                            then
                                                                                                                                                                                              (do
                                                                                                                                                                                                let w__135 ← (( do
                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                  )
                                                                                                                                                                                                  :
                                                                                                                                                                                                  SailM
                                                                                                                                                                                                  Int
                                                                                                                                                                                                  )
                                                                                                                                                                                                (pure (((w__135 <b 3279) : Bool))))
                                                                                                                                                                                            else
                                                                                                                                                                                              (pure false))
                                                                                                                                                                                        else
                                                                                                                                                                                          (pure false)
                                                                                                                                                                                        )
                                                                                                                                                                                        :
                                                                                                                                                                                        SailM
                                                                                                                                                                                        Bool
                                                                                                                                                                                        )
                                                                                                                                                                                      if (w__137 : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (do
                                                                                                                                                                                          writeReg SEE 3279
                                                                                                                                                                                          let cond :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              28
                                                                                                                                                                                              4)
                                                                                                                                                                                          let Rn :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              16
                                                                                                                                                                                              4)
                                                                                                                                                                                          let Rd :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              12
                                                                                                                                                                                              4)
                                                                                                                                                                                          let Rm :=
                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                              __opcode
                                                                                                                                                                                              0
                                                                                                                                                                                              4)
                                                                                                                                                                                          if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                         8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                         9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                       10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                     11)])) != 1#1)) : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                              ()))
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              (decode_aarch32_instrs_UADD16_A1enc_A_txt
                                                                                                                                                                                                cond
                                                                                                                                                                                                Rn
                                                                                                                                                                                                Rd
                                                                                                                                                                                                Rm)))
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          let w__140 ← (( do
                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                     27
                                                                                                                                                                                                     20)) == (0x65#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                     11
                                                                                                                                                                                                     4)) == (0xF9#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                                                            then
                                                                                                                                                                                              (do
                                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                       28
                                                                                                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                then
                                                                                                                                                                                                  (do
                                                                                                                                                                                                    let w__138 ← (( do
                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                      )
                                                                                                                                                                                                      :
                                                                                                                                                                                                      SailM
                                                                                                                                                                                                      Int
                                                                                                                                                                                                      )
                                                                                                                                                                                                    (pure (((w__138 <b 3281) : Bool))))
                                                                                                                                                                                                else
                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                            else
                                                                                                                                                                                              (pure false)
                                                                                                                                                                                            )
                                                                                                                                                                                            :
                                                                                                                                                                                            SailM
                                                                                                                                                                                            Bool
                                                                                                                                                                                            )
                                                                                                                                                                                          if (w__140 : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (do
                                                                                                                                                                                              writeReg SEE 3281
                                                                                                                                                                                              let cond :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  28
                                                                                                                                                                                                  4)
                                                                                                                                                                                              let Rn :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  16
                                                                                                                                                                                                  4)
                                                                                                                                                                                              let Rd :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  12
                                                                                                                                                                                                  4)
                                                                                                                                                                                              let Rm :=
                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                  0
                                                                                                                                                                                                  4)
                                                                                                                                                                                              if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                             8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                             9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                           10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                         11)])) != 1#1)) : Bool)
                                                                                                                                                                                              then
                                                                                                                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                  ()))
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  (decode_aarch32_instrs_UADD8_A1enc_A_txt
                                                                                                                                                                                                    cond
                                                                                                                                                                                                    Rn
                                                                                                                                                                                                    Rd
                                                                                                                                                                                                    Rm)))
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              let w__143 ← (( do
                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                         27
                                                                                                                                                                                                         20)) == (0x65#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                         11
                                                                                                                                                                                                         4)) == (0xF3#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                                                                then
                                                                                                                                                                                                  (do
                                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                           28
                                                                                                                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                    then
                                                                                                                                                                                                      (do
                                                                                                                                                                                                        let w__141 ← (( do
                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                          )
                                                                                                                                                                                                          :
                                                                                                                                                                                                          SailM
                                                                                                                                                                                                          Int
                                                                                                                                                                                                          )
                                                                                                                                                                                                        (pure (((w__141 <b 3283) : Bool))))
                                                                                                                                                                                                    else
                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                else
                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                )
                                                                                                                                                                                                :
                                                                                                                                                                                                SailM
                                                                                                                                                                                                Bool
                                                                                                                                                                                                )
                                                                                                                                                                                              if (w__143 : Bool)
                                                                                                                                                                                              then
                                                                                                                                                                                                (do
                                                                                                                                                                                                  writeReg SEE 3283
                                                                                                                                                                                                  let cond :=
                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                      28
                                                                                                                                                                                                      4)
                                                                                                                                                                                                  let Rn :=
                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                      16
                                                                                                                                                                                                      4)
                                                                                                                                                                                                  let Rd :=
                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                      12
                                                                                                                                                                                                      4)
                                                                                                                                                                                                  let Rm :=
                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                      0
                                                                                                                                                                                                      4)
                                                                                                                                                                                                  if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                               10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                             11)])) != 1#1)) : Bool)
                                                                                                                                                                                                  then
                                                                                                                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                      ()))
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      (decode_aarch32_instrs_UASX_A1enc_A_txt
                                                                                                                                                                                                        cond
                                                                                                                                                                                                        Rn
                                                                                                                                                                                                        Rd
                                                                                                                                                                                                        Rm)))
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  let w__146 ← (( do
                                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                             27
                                                                                                                                                                                                             21)) == (0b0111111#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                             6
                                                                                                                                                                                                             4)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                                                                    then
                                                                                                                                                                                                      (do
                                                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                               28
                                                                                                                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                        then
                                                                                                                                                                                                          (do
                                                                                                                                                                                                            let w__144 ← (( do
                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                              )
                                                                                                                                                                                                              :
                                                                                                                                                                                                              SailM
                                                                                                                                                                                                              Int
                                                                                                                                                                                                              )
                                                                                                                                                                                                            (pure (((w__144 <b 3285) : Bool))))
                                                                                                                                                                                                        else
                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                    else
                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                    )
                                                                                                                                                                                                    :
                                                                                                                                                                                                    SailM
                                                                                                                                                                                                    Bool
                                                                                                                                                                                                    )
                                                                                                                                                                                                  if (w__146 : Bool)
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      writeReg SEE 3285
                                                                                                                                                                                                      let cond :=
                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                          28
                                                                                                                                                                                                          4)
                                                                                                                                                                                                      let widthm1 :=
                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                          16
                                                                                                                                                                                                          5)
                                                                                                                                                                                                      let Rd :=
                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                          12
                                                                                                                                                                                                          4)
                                                                                                                                                                                                      let lsb :=
                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                          7
                                                                                                                                                                                                          5)
                                                                                                                                                                                                      let Rn :=
                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                          0
                                                                                                                                                                                                          4)
                                                                                                                                                                                                      (decode_aarch32_instrs_UBFX_A1enc_A_txt
                                                                                                                                                                                                        cond
                                                                                                                                                                                                        widthm1
                                                                                                                                                                                                        Rd
                                                                                                                                                                                                        lsb
                                                                                                                                                                                                        Rn))
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      let w__148 ← (( do
                                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                 31
                                                                                                                                                                                                                 20)) == (0xE7F#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                 7
                                                                                                                                                                                                                 4)) == (0xF#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                                                                                                                        then
                                                                                                                                                                                                          (do
                                                                                                                                                                                                            let w__147 ← (( do
                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                              )
                                                                                                                                                                                                              :
                                                                                                                                                                                                              SailM
                                                                                                                                                                                                              Int
                                                                                                                                                                                                              )
                                                                                                                                                                                                            (pure (((w__147 <b 3287) : Bool))))
                                                                                                                                                                                                        else
                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                        )
                                                                                                                                                                                                        :
                                                                                                                                                                                                        SailM
                                                                                                                                                                                                        Bool
                                                                                                                                                                                                        )
                                                                                                                                                                                                      if (w__148 : Bool)
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          writeReg SEE 3287
                                                                                                                                                                                                          let imm12 :=
                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                              8
                                                                                                                                                                                                              12)
                                                                                                                                                                                                          let imm4 :=
                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                              0
                                                                                                                                                                                                              4)
                                                                                                                                                                                                          (decode_aarch32_instrs_UDF_A1enc_A_txt
                                                                                                                                                                                                            imm12
                                                                                                                                                                                                            imm4))
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          let w__151 ← (( do
                                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                     27
                                                                                                                                                                                                                     20)) == (0x73#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                     7
                                                                                                                                                                                                                     4)) == (0x1#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                                                                                                                            then
                                                                                                                                                                                                              (do
                                                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                       28
                                                                                                                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                then
                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                    let w__149 ← (( do
                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                      )
                                                                                                                                                                                                                      :
                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                      )
                                                                                                                                                                                                                    (pure (((w__149 <b 3290) : Bool))))
                                                                                                                                                                                                                else
                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                            else
                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                            )
                                                                                                                                                                                                            :
                                                                                                                                                                                                            SailM
                                                                                                                                                                                                            Bool
                                                                                                                                                                                                            )
                                                                                                                                                                                                          if (w__151 : Bool)
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              writeReg SEE 3290
                                                                                                                                                                                                              let cond :=
                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                  28
                                                                                                                                                                                                                  4)
                                                                                                                                                                                                              let Rd :=
                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                  16
                                                                                                                                                                                                                  4)
                                                                                                                                                                                                              let Ra :=
                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                  12
                                                                                                                                                                                                                  4)
                                                                                                                                                                                                              let Rm :=
                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                  8
                                                                                                                                                                                                                  4)
                                                                                                                                                                                                              let Rn :=
                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                  0
                                                                                                                                                                                                                  4)
                                                                                                                                                                                                              (decode_aarch32_instrs_UDIV_A1enc_A_txt
                                                                                                                                                                                                                cond
                                                                                                                                                                                                                Rd
                                                                                                                                                                                                                Ra
                                                                                                                                                                                                                Rm
                                                                                                                                                                                                                Rn))
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              let w__154 ← (( do
                                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                         27
                                                                                                                                                                                                                         20)) == (0x67#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                         11
                                                                                                                                                                                                                         4)) == (0xF1#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                                                                                then
                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                           28
                                                                                                                                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                    then
                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                        let w__152 ← (( do
                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                          )
                                                                                                                                                                                                                          :
                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                          )
                                                                                                                                                                                                                        (pure (((w__152 <b 3292) : Bool))))
                                                                                                                                                                                                                    else
                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                else
                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                )
                                                                                                                                                                                                                :
                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                )
                                                                                                                                                                                                              if (w__154 : Bool)
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  writeReg SEE 3292
                                                                                                                                                                                                                  let cond :=
                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                      28
                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                  let Rn :=
                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                      16
                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                  let Rd :=
                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                      12
                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                  let Rm :=
                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                      0
                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                  if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                               10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                             11)])) != 1#1)) : Bool)
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                      ()))
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      (decode_aarch32_instrs_UHADD16_A1enc_A_txt
                                                                                                                                                                                                                        cond
                                                                                                                                                                                                                        Rn
                                                                                                                                                                                                                        Rd
                                                                                                                                                                                                                        Rm)))
                                                                                                                                                                                                              else
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  let w__157 ← (( do
                                                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                             27
                                                                                                                                                                                                                             20)) == (0x67#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                             11
                                                                                                                                                                                                                             4)) == (0xF9#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                                                                                    then
                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                               28
                                                                                                                                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                        then
                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                            let w__155 ← (( do
                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                              )
                                                                                                                                                                                                                              :
                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                              )
                                                                                                                                                                                                                            (pure (((w__155 <b 3294) : Bool))))
                                                                                                                                                                                                                        else
                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                    else
                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                    )
                                                                                                                                                                                                                    :
                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                    )
                                                                                                                                                                                                                  if (w__157 : Bool)
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      writeReg SEE 3294
                                                                                                                                                                                                                      let cond :=
                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                          28
                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                      let Rn :=
                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                          16
                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                      let Rd :=
                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                          12
                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                      let Rm :=
                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                          0
                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                      if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                     8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                     9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                   10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                 11)])) != 1#1)) : Bool)
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                          ()))
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          (decode_aarch32_instrs_UHADD8_A1enc_A_txt
                                                                                                                                                                                                                            cond
                                                                                                                                                                                                                            Rn
                                                                                                                                                                                                                            Rd
                                                                                                                                                                                                                            Rm)))
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      let w__160 ← (( do
                                                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                 27
                                                                                                                                                                                                                                 20)) == (0x67#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                 11
                                                                                                                                                                                                                                 4)) == (0xF3#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                                                                                        then
                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                   28
                                                                                                                                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                            then
                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                let w__158 ← (( do
                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                (pure (((w__158 <b 3296) : Bool))))
                                                                                                                                                                                                                            else
                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                        else
                                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                                        )
                                                                                                                                                                                                                        :
                                                                                                                                                                                                                        SailM
                                                                                                                                                                                                                        Bool
                                                                                                                                                                                                                        )
                                                                                                                                                                                                                      if (w__160 : Bool)
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          writeReg SEE 3296
                                                                                                                                                                                                                          let cond :=
                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                              28
                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                          let Rn :=
                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                              16
                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                          let Rd :=
                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                              12
                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                          let Rm :=
                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                              0
                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                          if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                         8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                         9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                       10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                     11)])) != 1#1)) : Bool)
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                              ()))
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              (decode_aarch32_instrs_UHASX_A1enc_A_txt
                                                                                                                                                                                                                                cond
                                                                                                                                                                                                                                Rn
                                                                                                                                                                                                                                Rd
                                                                                                                                                                                                                                Rm)))
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          let w__163 ← (( do
                                                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                     27
                                                                                                                                                                                                                                     20)) == (0x67#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                     11
                                                                                                                                                                                                                                     4)) == (0xF5#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                                                                                            then
                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                       28
                                                                                                                                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                    let w__161 ← (( do
                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                    (pure (((w__161 <b 3298) : Bool))))
                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                            else
                                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                                            )
                                                                                                                                                                                                                            :
                                                                                                                                                                                                                            SailM
                                                                                                                                                                                                                            Bool
                                                                                                                                                                                                                            )
                                                                                                                                                                                                                          if (w__163 : Bool)
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              writeReg SEE 3298
                                                                                                                                                                                                                              let cond :=
                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                  28
                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                              let Rn :=
                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                  16
                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                              let Rd :=
                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                  12
                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                              let Rm :=
                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                  0
                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                              if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                             8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                             9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                           10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                         11)])) != 1#1)) : Bool)
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                  ()))
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  (decode_aarch32_instrs_UHSAX_A1enc_A_txt
                                                                                                                                                                                                                                    cond
                                                                                                                                                                                                                                    Rn
                                                                                                                                                                                                                                    Rd
                                                                                                                                                                                                                                    Rm)))
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              let w__166 ← (( do
                                                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                         27
                                                                                                                                                                                                                                         20)) == (0x67#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                         11
                                                                                                                                                                                                                                         4)) == (0xF7#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                           28
                                                                                                                                                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                        let w__164 ← (( do
                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                        (pure (((w__164 <b 3300) : Bool))))
                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                :
                                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                                )
                                                                                                                                                                                                                              if (w__166 : Bool)
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  writeReg SEE 3300
                                                                                                                                                                                                                                  let cond :=
                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                      28
                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                  let Rn :=
                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                      16
                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                  let Rd :=
                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                      12
                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                  let Rm :=
                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                      0
                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                  if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                               10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                             11)])) != 1#1)) : Bool)
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                      ()))
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      (decode_aarch32_instrs_UHSUB16_A1enc_A_txt
                                                                                                                                                                                                                                        cond
                                                                                                                                                                                                                                        Rn
                                                                                                                                                                                                                                        Rd
                                                                                                                                                                                                                                        Rm)))
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  let w__169 ← (( do
                                                                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                             27
                                                                                                                                                                                                                                             20)) == (0x67#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                             11
                                                                                                                                                                                                                                             4)) == (0xFF#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                               28
                                                                                                                                                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                            let w__167 ← (( do
                                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                              :
                                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                            (pure (((w__167 <b 3302) : Bool))))
                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                    :
                                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                  if (w__169 : Bool)
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      writeReg SEE 3302
                                                                                                                                                                                                                                      let cond :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          28
                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                      let Rn :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          16
                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                      let Rd :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          12
                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                      let Rm :=
                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                          0
                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                      if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                     8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                     9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                                   10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                 11)])) != 1#1)) : Bool)
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                          ()))
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          (decode_aarch32_instrs_UHSUB8_A1enc_A_txt
                                                                                                                                                                                                                                            cond
                                                                                                                                                                                                                                            Rn
                                                                                                                                                                                                                                            Rd
                                                                                                                                                                                                                                            Rm)))
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      let w__172 ← (( do
                                                                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                 27
                                                                                                                                                                                                                                                 20)) == (0x66#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                 11
                                                                                                                                                                                                                                                 4)) == (0xF1#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                                   28
                                                                                                                                                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                let w__170 ← (( do
                                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                (pure (((w__170 <b 3310) : Bool))))
                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                        :
                                                                                                                                                                                                                                        SailM
                                                                                                                                                                                                                                        Bool
                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                      if (w__172 : Bool)
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          writeReg SEE 3310
                                                                                                                                                                                                                                          let cond :=
                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                              28
                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                          let Rn :=
                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                              16
                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                          let Rd :=
                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                              12
                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                          let Rm :=
                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                              0
                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                          if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                         8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                         9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                       10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                     11)])) != 1#1)) : Bool)
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                              ()))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              (decode_aarch32_instrs_UQADD16_A1enc_A_txt
                                                                                                                                                                                                                                                cond
                                                                                                                                                                                                                                                Rn
                                                                                                                                                                                                                                                Rd
                                                                                                                                                                                                                                                Rm)))
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          let w__175 ← (( do
                                                                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                     27
                                                                                                                                                                                                                                                     20)) == (0x66#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                     11
                                                                                                                                                                                                                                                     4)) == (0xF9#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                       28
                                                                                                                                                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                    let w__173 ← (( do
                                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                    (pure (((w__173 <b 3312) : Bool))))
                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                            :
                                                                                                                                                                                                                                            SailM
                                                                                                                                                                                                                                            Bool
                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                          if (w__175 : Bool)
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              writeReg SEE 3312
                                                                                                                                                                                                                                              let cond :=
                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                  28
                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                              let Rn :=
                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                  16
                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                              let Rd :=
                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                  12
                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                              let Rm :=
                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                  0
                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                              if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                             8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                             9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                                           10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                         11)])) != 1#1)) : Bool)
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                                  ()))
                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  (decode_aarch32_instrs_UQADD8_A1enc_A_txt
                                                                                                                                                                                                                                                    cond
                                                                                                                                                                                                                                                    Rn
                                                                                                                                                                                                                                                    Rd
                                                                                                                                                                                                                                                    Rm)))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              let w__178 ← (( do
                                                                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                         27
                                                                                                                                                                                                                                                         20)) == (0x66#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                         11
                                                                                                                                                                                                                                                         4)) == (0xF3#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                                           28
                                                                                                                                                                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                        let w__176 ← (( do
                                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                        (pure (((w__176 <b 3314) : Bool))))
                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                :
                                                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                              if (w__178 : Bool)
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  writeReg SEE 3314
                                                                                                                                                                                                                                                  let cond :=
                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                      28
                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                  let Rn :=
                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                      16
                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                  let Rd :=
                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                      12
                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                  let Rm :=
                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                      0
                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                  if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                                               10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                             11)])) != 1#1)) : Bool)
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                                      ()))
                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      (decode_aarch32_instrs_UQASX_A1enc_A_txt
                                                                                                                                                                                                                                                        cond
                                                                                                                                                                                                                                                        Rn
                                                                                                                                                                                                                                                        Rd
                                                                                                                                                                                                                                                        Rm)))
                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  let w__181 ← (( do
                                                                                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                             27
                                                                                                                                                                                                                                                             20)) == (0x66#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                             11
                                                                                                                                                                                                                                                             4)) == (0xF5#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                                               28
                                                                                                                                                                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                            let w__179 ← (( do
                                                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                              :
                                                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                            (pure (((w__179 <b 3316) : Bool))))
                                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                    :
                                                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                  if (w__181 : Bool)
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      writeReg SEE 3316
                                                                                                                                                                                                                                                      let cond :=
                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                          28
                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                      let Rn :=
                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                          16
                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                      let Rd :=
                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                          12
                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                      let Rm :=
                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                          0
                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                      if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                     8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                     9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                                                   10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                 11)])) != 1#1)) : Bool)
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                                          ()))
                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          (decode_aarch32_instrs_UQSAX_A1enc_A_txt
                                                                                                                                                                                                                                                            cond
                                                                                                                                                                                                                                                            Rn
                                                                                                                                                                                                                                                            Rd
                                                                                                                                                                                                                                                            Rm)))
                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      let w__184 ← (( do
                                                                                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                 27
                                                                                                                                                                                                                                                                 20)) == (0x66#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                 11
                                                                                                                                                                                                                                                                 4)) == (0xF7#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                                                   28
                                                                                                                                                                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                                let w__182 ← (( do
                                                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                (pure (((w__182 <b 3318) : Bool))))
                                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                        :
                                                                                                                                                                                                                                                        SailM
                                                                                                                                                                                                                                                        Bool
                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                      if (w__184 : Bool)
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          writeReg SEE 3318
                                                                                                                                                                                                                                                          let cond :=
                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                              28
                                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                                          let Rn :=
                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                              16
                                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                                          let Rd :=
                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                              12
                                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                                          let Rm :=
                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                              0
                                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                                          if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                         8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                         9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                                       10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                     11)])) != 1#1)) : Bool)
                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                                              ()))
                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              (decode_aarch32_instrs_UQSUB16_A1enc_A_txt
                                                                                                                                                                                                                                                                cond
                                                                                                                                                                                                                                                                Rn
                                                                                                                                                                                                                                                                Rd
                                                                                                                                                                                                                                                                Rm)))
                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          let w__187 ← (( do
                                                                                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                     27
                                                                                                                                                                                                                                                                     20)) == (0x66#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                     11
                                                                                                                                                                                                                                                                     4)) == (0xFF#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                                       28
                                                                                                                                                                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                    let w__185 ← (( do
                                                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                    (pure (((w__185 <b 3320) : Bool))))
                                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                            :
                                                                                                                                                                                                                                                            SailM
                                                                                                                                                                                                                                                            Bool
                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                          if (w__187 : Bool)
                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              writeReg SEE 3320
                                                                                                                                                                                                                                                              let cond :=
                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                  28
                                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                                              let Rn :=
                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                  16
                                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                                              let Rd :=
                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                  12
                                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                                              let Rm :=
                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                  0
                                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                                              if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                             8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                             9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                                                           10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                         11)])) != 1#1)) : Bool)
                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                                                  ()))
                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  (decode_aarch32_instrs_UQSUB8_A1enc_A_txt
                                                                                                                                                                                                                                                                    cond
                                                                                                                                                                                                                                                                    Rn
                                                                                                                                                                                                                                                                    Rd
                                                                                                                                                                                                                                                                    Rm)))
                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              let w__190 ← (( do
                                                                                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                         27
                                                                                                                                                                                                                                                                         20)) == (0x78#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                                                           15
                                                                                                                                                                                                                                                                           12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                                                           7
                                                                                                                                                                                                                                                                           4)) == (0x1#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                                                           28
                                                                                                                                                                                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                                        let w__188 ← (( do
                                                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                        (pure (((w__188 <b 3322) : Bool))))
                                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                :
                                                                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                              if (w__190 : Bool)
                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  writeReg SEE 3322
                                                                                                                                                                                                                                                                  let cond :=
                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                      28
                                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                                  let Rd :=
                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                      16
                                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                                  let Rm :=
                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                      8
                                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                                  let Rn :=
                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                      0
                                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                                  (decode_aarch32_instrs_USAD8_A1enc_A_txt
                                                                                                                                                                                                                                                                    cond
                                                                                                                                                                                                                                                                    Rd
                                                                                                                                                                                                                                                                    Rm
                                                                                                                                                                                                                                                                    Rn))
                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  let w__193 ← (( do
                                                                                                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                             27
                                                                                                                                                                                                                                                                             20)) == (0x78#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                             7
                                                                                                                                                                                                                                                                             4)) == (0x1#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                                                               28
                                                                                                                                                                                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                                            let w__191 ← (( do
                                                                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                              :
                                                                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                            (pure (((w__191 <b 3324) : Bool))))
                                                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                    :
                                                                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                  if (w__193 : Bool)
                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      writeReg SEE 3324
                                                                                                                                                                                                                                                                      let cond :=
                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                          28
                                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                                      let Rd :=
                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                          16
                                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                                      let Ra :=
                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                          12
                                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                                      let Rm :=
                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                          8
                                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                                      let Rn :=
                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                          0
                                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                                      (decode_aarch32_instrs_USADA8_A1enc_A_txt
                                                                                                                                                                                                                                                                        cond
                                                                                                                                                                                                                                                                        Rd
                                                                                                                                                                                                                                                                        Ra
                                                                                                                                                                                                                                                                        Rm
                                                                                                                                                                                                                                                                        Rn))
                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      let w__196 ← (( do
                                                                                                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                 27
                                                                                                                                                                                                                                                                                 20)) == (0x6E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                 11
                                                                                                                                                                                                                                                                                 4)) == (0xF3#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                                                                   28
                                                                                                                                                                                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                                                let w__194 ← (( do
                                                                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                (pure (((w__194 <b 3326) : Bool))))
                                                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                        :
                                                                                                                                                                                                                                                                        SailM
                                                                                                                                                                                                                                                                        Bool
                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                      if (w__196 : Bool)
                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          writeReg SEE 3326
                                                                                                                                                                                                                                                                          let cond :=
                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                              28
                                                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                                                          let sat_imm :=
                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                              16
                                                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                                                          let Rd :=
                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                              12
                                                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                                                          let Rn :=
                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                              0
                                                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                                                          if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                                         8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                                         9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                                                       10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                                     11)])) != 1#1)) : Bool)
                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                                                              ()))
                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              (decode_aarch32_instrs_USAT16_A1enc_A_txt
                                                                                                                                                                                                                                                                                cond
                                                                                                                                                                                                                                                                                sat_imm
                                                                                                                                                                                                                                                                                Rd
                                                                                                                                                                                                                                                                                Rn)))
                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          let w__199 ← (( do
                                                                                                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                                     27
                                                                                                                                                                                                                                                                                     21)) == (0b0110111#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                                     5
                                                                                                                                                                                                                                                                                     4)) == (0b01#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                                                       28
                                                                                                                                                                                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                                    let w__197 ← (( do
                                                                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                    (pure (((w__197 <b 3328) : Bool))))
                                                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                            :
                                                                                                                                                                                                                                                                            SailM
                                                                                                                                                                                                                                                                            Bool
                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                          if (w__199 : Bool)
                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              writeReg SEE 3328
                                                                                                                                                                                                                                                                              let cond :=
                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                  28
                                                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                                                              let sat_imm :=
                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                  16
                                                                                                                                                                                                                                                                                  5)
                                                                                                                                                                                                                                                                              let Rd :=
                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                  12
                                                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                                                              let imm5 :=
                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                  7
                                                                                                                                                                                                                                                                                  5)
                                                                                                                                                                                                                                                                              let sh :=
                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                  6
                                                                                                                                                                                                                                                                                  1)
                                                                                                                                                                                                                                                                              let Rn :=
                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                  0
                                                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                                                              (decode_aarch32_instrs_USAT_A1enc_A_txt
                                                                                                                                                                                                                                                                                cond
                                                                                                                                                                                                                                                                                sat_imm
                                                                                                                                                                                                                                                                                Rd
                                                                                                                                                                                                                                                                                imm5
                                                                                                                                                                                                                                                                                sh
                                                                                                                                                                                                                                                                                Rn))
                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              let w__202 ← (( do
                                                                                                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                                         27
                                                                                                                                                                                                                                                                                         20)) == (0x65#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                                         11
                                                                                                                                                                                                                                                                                         4)) == (0xF5#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                                                                           28
                                                                                                                                                                                                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                                                        let w__200 ← (( do
                                                                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                        (pure (((w__200 <b 3330) : Bool))))
                                                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                :
                                                                                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                              if (w__202 : Bool)
                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  writeReg SEE 3330
                                                                                                                                                                                                                                                                                  let cond :=
                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                      28
                                                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                                                  let Rn :=
                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                      16
                                                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                                                  let Rd :=
                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                      12
                                                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                                                  let Rm :=
                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                      0
                                                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                                                  if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                                 8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                                 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                                                                               10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                                             11)])) != 1#1)) : Bool)
                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                                                                      ()))
                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      (decode_aarch32_instrs_USAX_A1enc_A_txt
                                                                                                                                                                                                                                                                                        cond
                                                                                                                                                                                                                                                                                        Rn
                                                                                                                                                                                                                                                                                        Rd
                                                                                                                                                                                                                                                                                        Rm)))
                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  let w__205 ← (( do
                                                                                                                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                                             27
                                                                                                                                                                                                                                                                                             20)) == (0x65#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                                             11
                                                                                                                                                                                                                                                                                             4)) == (0xF7#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                                                                               28
                                                                                                                                                                                                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                                                            let w__203 ← (( do
                                                                                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                              :
                                                                                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                            (pure (((w__203 <b 3332) : Bool))))
                                                                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                    :
                                                                                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                  if (w__205 : Bool)
                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      writeReg SEE 3332
                                                                                                                                                                                                                                                                                      let cond :=
                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                          28
                                                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                                                      let Rn :=
                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                          16
                                                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                                                      let Rd :=
                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                          12
                                                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                                                      let Rm :=
                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                          0
                                                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                                                      if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                                                     8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                                                     9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                                                                                   10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                                 11)])) != 1#1)) : Bool)
                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                                                                          ()))
                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          (decode_aarch32_instrs_USUB16_A1enc_A_txt
                                                                                                                                                                                                                                                                                            cond
                                                                                                                                                                                                                                                                                            Rn
                                                                                                                                                                                                                                                                                            Rd
                                                                                                                                                                                                                                                                                            Rm)))
                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      let w__208 ← (( do
                                                                                                                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                                 27
                                                                                                                                                                                                                                                                                                 20)) == (0x65#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                                 11
                                                                                                                                                                                                                                                                                                 4)) == (0xFF#8 : (BitVec 8)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                                                                                   28
                                                                                                                                                                                                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                                                                let w__206 ← (( do
                                                                                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                (pure (((w__206 <b 3334) : Bool))))
                                                                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                        :
                                                                                                                                                                                                                                                                                        SailM
                                                                                                                                                                                                                                                                                        Bool
                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                      if (w__208 : Bool)
                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          writeReg SEE 3334
                                                                                                                                                                                                                                                                                          let cond :=
                                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                                              28
                                                                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                                                                          let Rn :=
                                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                                              16
                                                                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                                                                          let Rd :=
                                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                                              12
                                                                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                                                                          let Rm :=
                                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                                              0
                                                                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                                                                          if ((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                                                         8)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                                                         9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                                                                       10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                                                     11)])) != 1#1)) : Bool)
                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                                                                              ()))
                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              (decode_aarch32_instrs_USUB8_A1enc_A_txt
                                                                                                                                                                                                                                                                                                cond
                                                                                                                                                                                                                                                                                                Rn
                                                                                                                                                                                                                                                                                                Rd
                                                                                                                                                                                                                                                                                                Rm)))
                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          let w__211 ← (( do
                                                                                                                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                                                     27
                                                                                                                                                                                                                                                                                                     20)) == (0x6C#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                                                     9
                                                                                                                                                                                                                                                                                                     4)) == (0b000111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                                                                       28
                                                                                                                                                                                                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                                                    let w__209 ← (( do
                                                                                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                    (pure (((w__209 <b 3336) : Bool))))
                                                                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                            :
                                                                                                                                                                                                                                                                                            SailM
                                                                                                                                                                                                                                                                                            Bool
                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                          if (w__211 : Bool)
                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              writeReg SEE 3336
                                                                                                                                                                                                                                                                                              let cond :=
                                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                                  28
                                                                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                                                                              let Rn :=
                                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                                  16
                                                                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                                                                              let Rd :=
                                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                                  12
                                                                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                                                                              let rotate :=
                                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                                  10
                                                                                                                                                                                                                                                                                                  2)
                                                                                                                                                                                                                                                                                              let Rm :=
                                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                                  0
                                                                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                                                                              if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                                                         8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                                                         9)])) != 0#1)) : Bool)
                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                                                                                  ()))
                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  (decode_aarch32_instrs_UXTAB16_A1enc_A_txt
                                                                                                                                                                                                                                                                                                    cond
                                                                                                                                                                                                                                                                                                    Rn
                                                                                                                                                                                                                                                                                                    Rd
                                                                                                                                                                                                                                                                                                    rotate
                                                                                                                                                                                                                                                                                                    Rm)))
                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              let w__214 ← (( do
                                                                                                                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                                                         27
                                                                                                                                                                                                                                                                                                         20)) == (0x6E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                                                         9
                                                                                                                                                                                                                                                                                                         4)) == (0b000111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                                                                                           28
                                                                                                                                                                                                                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                                                                        let w__212 ← (( do
                                                                                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                        (pure (((w__212 <b 3338) : Bool))))
                                                                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                :
                                                                                                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                              if (w__214 : Bool)
                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  writeReg SEE 3338
                                                                                                                                                                                                                                                                                                  let cond :=
                                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                                      28
                                                                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                                                                  let Rn :=
                                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                                      16
                                                                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                                                                  let Rd :=
                                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                                      12
                                                                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                                                                  let rotate :=
                                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                                      10
                                                                                                                                                                                                                                                                                                      2)
                                                                                                                                                                                                                                                                                                  let Rm :=
                                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                                      0
                                                                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                                                                  if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                                                             8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                                                             9)])) != 0#1)) : Bool)
                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                                                                                      ()))
                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      (decode_aarch32_instrs_UXTAB_A1enc_A_txt
                                                                                                                                                                                                                                                                                                        cond
                                                                                                                                                                                                                                                                                                        Rn
                                                                                                                                                                                                                                                                                                        Rd
                                                                                                                                                                                                                                                                                                        rotate
                                                                                                                                                                                                                                                                                                        Rm)))
                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  let w__217 ← (( do
                                                                                                                                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                                                             27
                                                                                                                                                                                                                                                                                                             20)) == (0x6F#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                                                             9
                                                                                                                                                                                                                                                                                                             4)) == (0b000111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                                                                                               __opcode
                                                                                                                                                                                                                                                                                                               28
                                                                                                                                                                                                                                                                                                               4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                                                                            let w__215 ← (( do
                                                                                                                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                              :
                                                                                                                                                                                                                                                                                                              SailM
                                                                                                                                                                                                                                                                                                              Int
                                                                                                                                                                                                                                                                                                              )
                                                                                                                                                                                                                                                                                                            (pure (((w__215 <b 3340) : Bool))))
                                                                                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                    :
                                                                                                                                                                                                                                                                                                    SailM
                                                                                                                                                                                                                                                                                                    Bool
                                                                                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                                                                                  if (w__217 : Bool)
                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      writeReg SEE 3340
                                                                                                                                                                                                                                                                                                      let cond :=
                                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                                          28
                                                                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                                                                      let Rn :=
                                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                                          16
                                                                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                                                                      let Rd :=
                                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                                          12
                                                                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                                                                      let rotate :=
                                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                                          10
                                                                                                                                                                                                                                                                                                          2)
                                                                                                                                                                                                                                                                                                      let Rm :=
                                                                                                                                                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                                                                                                                                                          __opcode
                                                                                                                                                                                                                                                                                                          0
                                                                                                                                                                                                                                                                                                          4)
                                                                                                                                                                                                                                                                                                      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                                                 8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                                                 9)])) != 0#1)) : Bool)
                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                                                                                          ()))
                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          (decode_aarch32_instrs_UXTAH_A1enc_A_txt
                                                                                                                                                                                                                                                                                                            cond
                                                                                                                                                                                                                                                                                                            Rn
                                                                                                                                                                                                                                                                                                            Rd
                                                                                                                                                                                                                                                                                                            rotate
                                                                                                                                                                                                                                                                                                            Rm)))
                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      let w__220 ← (( do
                                                                                                                                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                                                 27
                                                                                                                                                                                                                                                                                                                 16)) == (0x6CF#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                                                                                                                 9
                                                                                                                                                                                                                                                                                                                 4)) == (0b000111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                        then
                                                                                                                                                                                                                                                                                                          (do
                                                                                                                                                                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                                                                                                   __opcode
                                                                                                                                                                                                                                                                                                                   28
                                                                                                                                                                                                                                                                                                                   4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                                                                                let w__218 ← (( do
                                                                                                                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                  :
                                                                                                                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                                                                                                                  )
                                                                                                                                                                                                                                                                                                                (pure (((w__218 <b 3342) : Bool))))
                                                                                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                                                                                                                        else
                                                                                                                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                        :
                                                                                                                                                                                                                                                                                                        SailM
                                                                                                                                                                                                                                                                                                        Bool
                                                                                                                                                                                                                                                                                                        )
                                                                                                                                                                                                                                                                                                      if (w__220 : Bool)
                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          writeReg SEE 3342
                                                                                                                                                                                                                                                                                                          let cond :=
                                                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                                                              28
                                                                                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                                                                                          let Rd :=
                                                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                                                              12
                                                                                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                                                                                          let rotate :=
                                                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                                                              10
                                                                                                                                                                                                                                                                                                              2)
                                                                                                                                                                                                                                                                                                          let Rm :=
                                                                                                                                                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                                                                                                                                                              __opcode
                                                                                                                                                                                                                                                                                                              0
                                                                                                                                                                                                                                                                                                              4)
                                                                                                                                                                                                                                                                                                          if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                                                                     8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                                                                     9)])) != 0#1)) : Bool)
                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                            sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                                                                                              ()))
                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                              (decode_aarch32_instrs_UXTB16_A1enc_A_txt
                                                                                                                                                                                                                                                                                                                cond
                                                                                                                                                                                                                                                                                                                Rd
                                                                                                                                                                                                                                                                                                                rotate
                                                                                                                                                                                                                                                                                                                Rm)))
                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          let w__223 ← (( do
                                                                                                                                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                                                                     27
                                                                                                                                                                                                                                                                                                                     16)) == (0x6EF#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                                                                                                                     9
                                                                                                                                                                                                                                                                                                                     4)) == (0b000111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                            then
                                                                                                                                                                                                                                                                                                              (do
                                                                                                                                                                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                                                                                                       __opcode
                                                                                                                                                                                                                                                                                                                       28
                                                                                                                                                                                                                                                                                                                       4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                                                                    let w__221 ← (( do
                                                                                                                                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                      :
                                                                                                                                                                                                                                                                                                                      SailM
                                                                                                                                                                                                                                                                                                                      Int
                                                                                                                                                                                                                                                                                                                      )
                                                                                                                                                                                                                                                                                                                    (pure (((w__221 <b 3344) : Bool))))
                                                                                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                                                                                                                                            else
                                                                                                                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                            :
                                                                                                                                                                                                                                                                                                            SailM
                                                                                                                                                                                                                                                                                                            Bool
                                                                                                                                                                                                                                                                                                            )
                                                                                                                                                                                                                                                                                                          if (w__223 : Bool)
                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                              writeReg SEE 3344
                                                                                                                                                                                                                                                                                                              let cond :=
                                                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                                                  28
                                                                                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                                                                                              let Rd :=
                                                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                                                  12
                                                                                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                                                                                              let rotate :=
                                                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                                                  10
                                                                                                                                                                                                                                                                                                                  2)
                                                                                                                                                                                                                                                                                                              let Rm :=
                                                                                                                                                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                                                                                                                                                  __opcode
                                                                                                                                                                                                                                                                                                                  0
                                                                                                                                                                                                                                                                                                                  4)
                                                                                                                                                                                                                                                                                                              if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                                                                         8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                                                                         9)])) != 0#1)) : Bool)
                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                                                                                                  ()))
                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                  (decode_aarch32_instrs_UXTB_A1enc_A_txt
                                                                                                                                                                                                                                                                                                                    cond
                                                                                                                                                                                                                                                                                                                    Rd
                                                                                                                                                                                                                                                                                                                    rotate
                                                                                                                                                                                                                                                                                                                    Rm)))
                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                              let w__226 ← (( do
                                                                                                                                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                                                                         27
                                                                                                                                                                                                                                                                                                                         16)) == (0x6FF#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                                                                                                                                         9
                                                                                                                                                                                                                                                                                                                         4)) == (0b000111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                                then
                                                                                                                                                                                                                                                                                                                  (do
                                                                                                                                                                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 4) (BitVec.slice
                                                                                                                                                                                                                                                                                                                           __opcode
                                                                                                                                                                                                                                                                                                                           28
                                                                                                                                                                                                                                                                                                                           4)) != 0b1111#4) : Bool) : Bool)
                                                                                                                                                                                                                                                                                                                    then
                                                                                                                                                                                                                                                                                                                      (do
                                                                                                                                                                                                                                                                                                                        let w__224 ← (( do
                                                                                                                                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                          :
                                                                                                                                                                                                                                                                                                                          SailM
                                                                                                                                                                                                                                                                                                                          Int
                                                                                                                                                                                                                                                                                                                          )
                                                                                                                                                                                                                                                                                                                        (pure (((w__224 <b 3347) : Bool))))
                                                                                                                                                                                                                                                                                                                    else
                                                                                                                                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                                                                                                                                else
                                                                                                                                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                                :
                                                                                                                                                                                                                                                                                                                SailM
                                                                                                                                                                                                                                                                                                                Bool
                                                                                                                                                                                                                                                                                                                )
                                                                                                                                                                                                                                                                                                              if (w__226 : Bool)
                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                  writeReg SEE 3347
                                                                                                                                                                                                                                                                                                                  let cond :=
                                                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                                                      28
                                                                                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                                                                                  let Rd :=
                                                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                                                      12
                                                                                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                                                                                  let rotate :=
                                                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                                                      10
                                                                                                                                                                                                                                                                                                                      2)
                                                                                                                                                                                                                                                                                                                  let Rm :=
                                                                                                                                                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                                                                                                                                                      __opcode
                                                                                                                                                                                                                                                                                                                      0
                                                                                                                                                                                                                                                                                                                      4)
                                                                                                                                                                                                                                                                                                                  if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                                                                             8)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                                                                                                                                             9)])) != 0#1)) : Bool)
                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                                                                                                                                                      ()))
                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                      (decode_aarch32_instrs_UXTH_A1enc_A_txt
                                                                                                                                                                                                                                                                                                                        cond
                                                                                                                                                                                                                                                                                                                        Rd
                                                                                                                                                                                                                                                                                                                        rotate
                                                                                                                                                                                                                                                                                                                        Rm)))
                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                sailThrow ((Error_Undefined
                                                                                                                                                                                                                                                                                                                  ())))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
