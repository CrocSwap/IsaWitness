import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0011
import ArmFull.Fn.M0012
import ArmFull.Fn.M0016
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0036
import ArmFull.Fn.M0038
import ArmFull.Fn.M0039
import ArmFull.Fn.M0040
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0046
import ArmFull.Fn.M0047
import ArmFull.Fn.M0048
import ArmFull.Fn.M0049
import ArmFull.Fn.M0087
import ArmFull.Fn.M0097
import ArmFull.Fn.M0117
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0153
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0179
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
import ArmFull.Fn.M0184
import ArmFull.Fn.M0186
import ArmFull.Fn.M0187
import ArmFull.Fn.M0196
import ArmFull.Fn.M0197
import ArmFull.Fn.M0198
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203

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

def BigEndian (acctype : AccessType) : SailM Bool := do
  let bigend ← (( do (undefined_bool_at (← occLabel 739) ()) ) : SailM Bool )
  let w__1 ← (( do
    (pure ((← do
          (HaveNV2Ext ())) && ((BEq.beq acctype AccessType_NV2) : Bool))) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
      (pure (((_get_SCTLR_EL2_Type_EE w__2) == 1#1))))
  else
    (do
      let w__3 ← (( do (UsingAArch32 ()) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          let bigend := ((w__4.E != 0#1) : Bool)
          (pure (bigend)))
      else
        (do
          let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((w__5.EL == EL0) : Bool)
          then
            (do
              let w__6 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
              let bigend := (((_get_SCTLRType_E0E w__6) != 0#1) : Bool)
              (pure (bigend)))
          else
            (do
              let w__7 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
              let bigend := (((_get_SCTLRType_EE w__7) != 0#1) : Bool)
              (pure (bigend)))))


def GenMPAMcurEL (acctype : AccessType) : SailM MPAMinfo := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  (GenMPAMatEL acctype w__0.EL)


def ASID_read (_ : Unit) : SailM (BitVec 16) := do
  let w__5 ← (( do
    if ((← do
         if ((← do
              (EL2Enabled ())) : Bool)
         then
           (do
             let w__1 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
             (pure (((! w__1) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure (((((_get_HCR_EL2_Type_E2H w__3) +++ (_get_HCR_EL2_Type_TGE w__4)) == 0b11#2) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      let w__6 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
      if (((_get_TCR_EL2_Type_A1 w__6) == 1#1) : Bool)
      then
        (do
          let w__7 ← (( do readReg TTBR1_EL2 ) : SailM (BitVec 128) )
          (pure ((_get_TTBR1_EL2_Type_ASID w__7))))
      else
        (do
          let w__8 ← (( do (TTBR0_EL2_read ()) ) : SailM (BitVec 128) )
          (pure ((_get_TTBR0_EL2_Type_ASID w__8)))))
  else
    (do
      let w__10 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
      if ((! w__10) : Bool)
      then
        (do
          let w__11 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
          if (((_get_TCR_EL1_Type_A1 w__11) == 1#1) : Bool)
          then
            (do
              let w__12 ← (( do (TTBR1_EL1_read ()) ) : SailM (BitVec 128) )
              (pure ((_get_TTBR1_EL1_Type_ASID w__12))))
          else
            (do
              let w__13 ← (( do (TTBR0_EL1_read ()) ) : SailM (BitVec 128) )
              (pure ((_get_TTBR0_EL1_Type_ASID w__13)))))
      else
        (do
          let w__15 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
          if (((_get_TTBCR_Type_EAE w__15) == 0#1) : Bool)
          then
            (do
              let w__16 ← (( do (CONTEXTIDR_read ()) ) : SailM (BitVec 32) )
              (pure ((Sail.BitVec.zeroExtend (_get_CONTEXTIDR_Type_ASID w__16) 16))))
          else
            (do
              let w__17 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
              if (((_get_TTBCR_Type_A1 w__17) == 1#1) : Bool)
              then
                (do
                  let w__18 ← (( do (TTBR1_read ()) ) : SailM (BitVec 64) )
                  (pure ((Sail.BitVec.zeroExtend (_get_TTBR1_Type_ASID w__18) 16))))
              else
                (do
                  let w__19 ← (( do (TTBR0_read ()) ) : SailM (BitVec 64) )
                  (pure ((Sail.BitVec.zeroExtend (_get_TTBR0_Type_ASID w__19) 16)))))))


def AArch32_EnterModeInDebugState (target_mode : (BitVec 5)) : SailM Unit := do
  let _ : Unit := (SynchronizeContext ())
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL1)) : Bool)
    then
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__1.EL != EL2) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__2 "sail-arm/v8_base.sail:14014.49-14014.50"
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__3.M == M32_Monitor) : Bool)
  then
    (do
      let w__4 ← (( do readReg SCR ) : SailM (BitVec 32) )
      writeReg SCR (Sail.BitVec.updateSubrange w__4 0 0 0#1))
  else (pure (()))
  (AArch32_WriteMode target_mode)
  let w__5 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  (SPSR_set (N := 32) w__5)
  let w__6 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  (R_set 14 w__6)
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with T := 1#1 }
  let split_vec ← (( do (__UNKNOWN_bits 4) ) : SailM (BitVec 4) )
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with SS := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__9 with A := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__10 with I := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__11 with F := (Sail.BitVec.extractLsb split_vec 0 0) }
  let w__12 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  (DLR_write w__12)
  let w__13 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  (DSPSR_write (Mk_DSPSR_Type w__13))
  let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__15 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  writeReg PSTATE { w__14 with E := (_get_SCTLR_Type_EE w__15) }
  let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__16 with IL := 0#1 }
  let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__17 with IT := 0b00000000#8 }
  let w__20 ← (( do
    if ((← do
         (HavePANExt ())) : Bool)
    then
      (do
        let w__19 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
        (pure ((((_get_SCTLR_Type_SPAN w__19) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__20 : Bool)
  then
    (do
      let w__21 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__21 with PAN := 1#1 })
  else (pure (()))
  let w__22 ← (( do (HaveSSBSExt ()) ) : SailM Bool )
  if (w__22 : Bool)
  then
    (do
      let w__23 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__24 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
      writeReg PSTATE { w__23 with SSBS := w__24 })
  else (pure (()))
  let w__25 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  (EDSCR_write (_update_EDSCR_Type_ERR w__25 1#1))
  (UpdateEDSCRFields ())
  (EndOfInstruction ())


def AArch32_EnterMonitorModeInDebugState (_ : Unit) : SailM Unit := do
  let _ : Unit := (SynchronizeContext ())
  let w__1 ← (( do
    if (((HaveEL EL3) : Bool) : Bool)
    then
      (do
        (ELUsingAArch32 EL3))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__1 "sail-arm/v8_base.sail:14094.44-14094.45"
  let w__2 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
  let from_secure : Bool := (BEq.beq w__2 SS_Secure)
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__3.M == M32_Monitor) : Bool)
  then
    (do
      let w__4 ← (( do readReg SCR ) : SailM (BitVec 32) )
      writeReg SCR (Sail.BitVec.updateSubrange w__4 0 0 0#1))
  else (pure (()))
  (AArch32_WriteMode M32_Monitor)
  let w__5 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  (SPSR_set (N := 32) w__5)
  let w__6 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  (R_set 14 w__6)
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with T := 1#1 }
  let split_vec ← (( do (__UNKNOWN_bits 4) ) : SailM (BitVec 4) )
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with SS := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__9 with A := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__10 with I := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__11 with F := (Sail.BitVec.extractLsb split_vec 0 0) }
  let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__13 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  writeReg PSTATE { w__12 with E := (_get_SCTLR_Type_EE w__13) }
  let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__14 with IL := 0#1 }
  let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__15 with IT := 0b00000000#8 }
  let w__16 ← (( do (HavePANExt ()) ) : SailM Bool )
  if (w__16 : Bool)
  then
    (do
      if ((! from_secure) : Bool)
      then
        (do
          let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__17 with PAN := 0#1 })
      else
        (do
          let w__18 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
          if (((_get_SCTLR_Type_SPAN w__18) == 0#1) : Bool)
          then
            (do
              let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__19 with PAN := 1#1 })
          else (pure (()))))
  else (pure (()))
  let w__20 ← (( do (HaveSSBSExt ()) ) : SailM Bool )
  if (w__20 : Bool)
  then
    (do
      let w__21 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__22 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
      writeReg PSTATE { w__21 with SSBS := w__22 })
  else (pure (()))
  let w__23 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  (DLR_write w__23)
  let w__24 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  (DSPSR_write (Mk_DSPSR_Type w__24))
  let w__25 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  (EDSCR_write (_update_EDSCR_Type_ERR w__25 1#1))
  (UpdateEDSCRFields ())
  (EndOfInstruction ())


def GenericCounterTick (_ : Unit) : SailM Unit := do
  let w__0 ← (( do readReg CNTCR ) : SailM (BitVec 32) )
  if (((_get_CNTCR_Type_EN w__0) == 0#1) : Bool)
  then
    (do
      let w__1 ← (( do (HaveAArch64 ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then
        (do
          (AArch32_CheckTimerConditions ()))
      else
        (do
          (AArch64_CheckTimerConditions ())))
  else
    (do
      let prev_physical_count ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
      let w__4 ← (( do
        if ((← do
             (HaveCNTSCExt ())) : Bool)
        then
          (do
            let w__3 ← (( do readReg CNTCR ) : SailM (BitVec 32) )
            (pure ((((_get_CNTCR_Type_SCEN w__3) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__5 ← (( do readReg PhysicalCount ) : SailM (BitVec 88) )
          let w__6 ← (( do readReg CNTSCR ) : SailM (BitVec 32) )
          writeReg PhysicalCount (w__5 + (Sail.BitVec.castWidth (m := 88) (Sail.BitVec.zeroExtend
              w__6 88))))
      else
        (do
          let w__7 ← (( do readReg PhysicalCount ) : SailM (BitVec 88) )
          let w__8 ← (( do readReg PhysicalCount ) : SailM (BitVec 88) )
          writeReg PhysicalCount (Sail.BitVec.updateSubrange w__7 87 24
            (BitVec.addInt (Sail.BitVec.extractLsb w__8 87 24) 1)))
      let w__9 ← (( do (HaveAArch64 ()) ) : SailM Bool )
      if ((! w__9) : Bool)
      then
        (do
          (AArch32_CheckTimerConditions ()))
      else
        (do
          (AArch64_CheckTimerConditions ()))
      let w__10 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
      (TestEventCNTP prev_physical_count w__10)
      let w__11 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
      (TestEventCNTV prev_physical_count w__11))


def AArch64_S1TTWParamsEL10 (varange : VARange) : SailM S1TTWParams := do
  let walkparams ← (( do (undefined_S1TTWParams (← occLabel 1260) ()) ) : SailM S1TTWParams )
  let w__2 ← (( do
    if ((← do
         (Have128BitDescriptorExt ())) : Bool)
    then
      (do
        (IsTCR2EL1Enabled ()))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__2 : Bool)
    then
      (do
        let w__3 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with d128 := (_get_TCR2_EL1_Type_D128 w__3) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with d128 := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let walkparams ← (( do
    if ((BEq.beq varange VARange_LOWER) : Bool)
    then
      (do
        let w__4 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
        let w__5 ← (( do (AArch64_S1DecodeTG0 (_get_TCR_EL1_Type_TG0 w__4)) ) : SailM TGx )
        let walkparams := ({ walkparams with tgx := w__5 } : S1TTWParams)
        let w__6 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with txsz := (_get_TCR_EL1_Type_T0SZ w__6) } : S1TTWParams)
        let w__7 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with irgn := (_get_TCR_EL1_Type_IRGN0 w__7) } : S1TTWParams)
        let w__8 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with orgn := (_get_TCR_EL1_Type_ORGN0 w__8) } : S1TTWParams)
        let w__9 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with sh := (_get_TCR_EL1_Type_SH0 w__9) } : S1TTWParams)
        let w__10 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with tbi := (_get_TCR_EL1_Type_TBI0 w__10) } : S1TTWParams)
        let w__13 ← (( do
          if ((← do
               (HaveSVE ())) : Bool)
          then (pure true)
          else
            (do
              (HaveTME ())) ) : SailM Bool )
        let w__15 ← (( do
          if (w__13 : Bool)
          then
            (do
              let w__14 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_NFD0 w__14))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with nfd := w__15 } : S1TTWParams)
        let w__16 ← (( do (HavePACExt ()) ) : SailM Bool )
        let w__18 ← (( do
          if (w__16 : Bool)
          then
            (do
              let w__17 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_TBID0 w__17))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with tbid := w__18 } : S1TTWParams)
        let w__19 ← (( do (HaveE0PDExt ()) ) : SailM Bool )
        let w__21 ← (( do
          if (w__19 : Bool)
          then
            (do
              let w__20 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_E0PD0 w__20))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with e0pd := w__21 } : S1TTWParams)
        let w__22 ← (( do (AArch64_HaveHPDExt ()) ) : SailM Bool )
        let w__24 ← (( do
          if (w__22 : Bool)
          then
            (do
              let w__23 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_HPD0 w__23))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with hpd := w__24 } : S1TTWParams)
        let w__25 ← (( do (HaveMTE4Ext ()) ) : SailM Bool )
        let w__27 ← (( do
          if (w__25 : Bool)
          then
            (do
              let w__26 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_MTX0 w__26))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with mtx := w__27 } : S1TTWParams)
        let w__29 ← (( do
          if ((walkparams.d128 == 1#1) : Bool)
          then
            (do
              let w__28 ← (( do (TTBR0_EL1_read ()) ) : SailM (BitVec 128) )
              (pure ((_get_TTBR0_EL1_Type_SKL w__28))))
          else (pure (0b00#2)) ) : SailM (BitVec 2) )
        let walkparams := ({ walkparams with skl := w__29 } : S1TTWParams)
        let w__31 ← (( do
          if ((walkparams.d128 == 1#1) : Bool)
          then
            (do
              let w__30 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR2_EL1_Type_DisCH0 w__30))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with disch := w__31 } : S1TTWParams)
        (pure (walkparams)))
    else
      (do
        let w__32 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
        let w__33 ← (( do (AArch64_S1DecodeTG1 (_get_TCR_EL1_Type_TG1 w__32)) ) : SailM TGx )
        let walkparams := ({ walkparams with tgx := w__33 } : S1TTWParams)
        let w__34 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with txsz := (_get_TCR_EL1_Type_T1SZ w__34) } : S1TTWParams)
        let w__35 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with irgn := (_get_TCR_EL1_Type_IRGN1 w__35) } : S1TTWParams)
        let w__36 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with orgn := (_get_TCR_EL1_Type_ORGN1 w__36) } : S1TTWParams)
        let w__37 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with sh := (_get_TCR_EL1_Type_SH1 w__37) } : S1TTWParams)
        let w__38 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with tbi := (_get_TCR_EL1_Type_TBI1 w__38) } : S1TTWParams)
        let w__41 ← (( do
          if ((← do
               (HaveSVE ())) : Bool)
          then (pure true)
          else
            (do
              (HaveTME ())) ) : SailM Bool )
        let w__43 ← (( do
          if (w__41 : Bool)
          then
            (do
              let w__42 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_NFD1 w__42))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with nfd := w__43 } : S1TTWParams)
        let w__44 ← (( do (HavePACExt ()) ) : SailM Bool )
        let w__46 ← (( do
          if (w__44 : Bool)
          then
            (do
              let w__45 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_TBID1 w__45))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with tbid := w__46 } : S1TTWParams)
        let w__47 ← (( do (HaveE0PDExt ()) ) : SailM Bool )
        let w__49 ← (( do
          if (w__47 : Bool)
          then
            (do
              let w__48 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_E0PD1 w__48))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with e0pd := w__49 } : S1TTWParams)
        let w__50 ← (( do (AArch64_HaveHPDExt ()) ) : SailM Bool )
        let w__52 ← (( do
          if (w__50 : Bool)
          then
            (do
              let w__51 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_HPD1 w__51))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with hpd := w__52 } : S1TTWParams)
        let w__53 ← (( do (HaveMTE4Ext ()) ) : SailM Bool )
        let w__55 ← (( do
          if (w__53 : Bool)
          then
            (do
              let w__54 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_MTX1 w__54))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with mtx := w__55 } : S1TTWParams)
        let w__57 ← (( do
          if ((walkparams.d128 == 1#1) : Bool)
          then
            (do
              let w__56 ← (( do (TTBR1_EL1_read ()) ) : SailM (BitVec 128) )
              (pure ((_get_TTBR1_EL1_Type_SKL w__56))))
          else (pure (0b00#2)) ) : SailM (BitVec 2) )
        let walkparams := ({ walkparams with skl := w__57 } : S1TTWParams)
        let w__59 ← (( do
          if ((walkparams.d128 == 1#1) : Bool)
          then
            (do
              let w__58 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR2_EL1_Type_DisCH1 w__58))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with disch := w__59 } : S1TTWParams)
        (pure (walkparams))) ) : SailM S1TTWParams )
  let w__60 ← (( do readReg MAIR_EL1 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with mair := (Mk_MAIRType w__60) } : S1TTWParams)
  let w__61 ← (( do (HaveAIEExt ()) ) : SailM Bool )
  let walkparams ← (( do
    if (w__61 : Bool)
    then
      (do
        let w__62 ← (( do readReg MAIR2_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with mair2 := (Mk_MAIRType w__62) } : S1TTWParams)
        (pure (walkparams)))
    else (pure (walkparams)) ) : SailM S1TTWParams )
  let w__65 ← (( do
    if ((← do
         (HaveAIEExt ())) : Bool)
    then
      (do
        (IsTCR2EL1Enabled ()))
    else (pure false) ) : SailM Bool )
  let w__67 ← (( do
    if (w__65 : Bool)
    then
      (do
        let w__66 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
        (pure ((_get_TCR2_EL1_Type_AIE w__66))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with aie := w__67 } : S1TTWParams)
  let w__68 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with wxn := (_get_SCTLR_EL1_Type_WXN w__68) } : S1TTWParams)
  let w__69 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with ps := (_get_TCR_EL1_Type_IPS w__69) } : S1TTWParams)
  let w__70 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let walkparams := ({ walkparams with ee := (_get_SCTLR_EL1_Type_EE w__70) } : S1TTWParams)
  let w__74 ← (( do
    if (((HaveEL EL3) : Bool) : Bool)
    then
      (do
        if ((← do
             let w__71 ← (( do (HaveRME ()) ) : SailM Bool )
             (pure (((! w__71) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            (HaveSecureEL2Ext ())))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__74 : Bool)
    then
      (do
        let w__75 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with sif := (_get_SCR_EL3_Type_SIF w__75) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with sif := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__76 ← (( do (EL2Enabled ()) ) : SailM Bool )
  let walkparams ← (( do
    if (w__76 : Bool)
    then
      (do
        let w__77 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with dc := (_get_HCR_EL2_Type_DC w__77) } : S1TTWParams)
        let w__78 ← (( do (HaveMTE2Ext ()) ) : SailM Bool )
        let w__80 ← (( do
          if (w__78 : Bool)
          then
            (do
              let w__79 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_HCR_EL2_Type_DCT w__79))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with dct := w__80 } : S1TTWParams)
        (pure (walkparams)))
    else (pure (walkparams)) ) : SailM S1TTWParams )
  let w__81 ← (( do (HaveTrapLoadStoreMultipleDeviceExt ()) ) : SailM Bool )
  let walkparams ← (( do
    if (w__81 : Bool)
    then
      (do
        let w__82 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with ntlsmd := (_get_SCTLR_EL1_Type_nTLSMD w__82) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with ntlsmd := 1#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__83 ← (( do (EL2Enabled ()) ) : SailM Bool )
  let walkparams ← (( do
    if (w__83 : Bool)
    then
      (do
        let w__84 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        let w__85 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        if ((((_get_HCR_EL2_Type_NV w__84) +++ (_get_HCR_EL2_Type_NV1 w__85)) == 0b01#2) : Bool)
        then
          (do
            let w__86 ← (( do (ConstrainUnpredictable Unpredictable_NVNV1) ) : SailM Constraint )
            let walkparams : S1TTWParams :=
              match w__86 with
              | .Constraint_NVNV1_00 => { walkparams with nv1 := 0#1 }
              | .Constraint_NVNV1_01 => { walkparams with nv1 := 1#1 }
              | .Constraint_NVNV1_11 => { walkparams with nv1 := 1#1 }
              | _ => walkparams
            (pure (walkparams)))
        else
          (do
            let w__87 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            let walkparams :=
              ({ walkparams with nv1 := (_get_HCR_EL2_Type_NV1 w__87) } : S1TTWParams)
            (pure (walkparams))))
    else
      (let walkparams : S1TTWParams := { walkparams with nv1 := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__88 ← (( do (HaveFeatCMOW ()) ) : SailM Bool )
  let w__90 ← (( do
    if (w__88 : Bool)
    then
      (do
        let w__89 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
        (pure ((_get_SCTLR_EL1_Type_CMOW w__89))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with cmow := w__90 } : S1TTWParams)
  let w__91 ← (( do (HaveAccessFlagUpdateExt ()) ) : SailM Bool )
  let w__93 ← (( do
    if (w__91 : Bool)
    then
      (do
        let w__92 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL1_Type_HA w__92))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with ha := w__93 } : S1TTWParams)
  let w__94 ← (( do (HaveDirtyBitModifierExt ()) ) : SailM Bool )
  let w__96 ← (( do
    if (w__94 : Bool)
    then
      (do
        let w__95 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
        (pure ((_get_TCR_EL1_Type_HD w__95))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with hd := w__96 } : S1TTWParams)
  let w__98 ← (( do
    if ((((BEq.beq walkparams.tgx TGx_4KB) || (BEq.beq walkparams.tgx TGx_16KB)) : Bool) : Bool)
    then
      (do
        (Have52BitIPAAndPASpaceExt ()))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__98 : Bool)
    then
      (do
        let w__99 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with ds := (_get_TCR_EL1_Type_DS w__99) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with ds := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let walkparams ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (let walkparams : S1TTWParams := { walkparams with pie := 1#1 }
      (pure (walkparams)))
    else
      (do
        let w__102 ← (( do
          if ((← do
               (HaveS1PIExt ())) : Bool)
          then
            (do
              (IsTCR2EL1Enabled ()))
          else (pure false) ) : SailM Bool )
        let w__104 ← (( do
          if (w__102 : Bool)
          then
            (do
              let w__103 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR2_EL1_Type_PIE w__103))))
          else (pure (0#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with pie := w__104 } : S1TTWParams)
        (pure (walkparams))) ) : SailM S1TTWParams )
  let w__105 ← (( do (HaveS1PIExt ()) ) : SailM Bool )
  let walkparams ← (( do
    if (w__105 : Bool)
    then
      (do
        let w__106 ← (( do readReg PIR_EL1 ) : SailM (BitVec 64) )
        let walkparams := ({ walkparams with pir := (Mk_S1PIRType w__106) } : S1TTWParams)
        if ((walkparams.nv1 != 1#1) : Bool)
        then
          (do
            let w__107 ← (( do readReg PIRE0_EL1 ) : SailM (BitVec 64) )
            let walkparams := ({ walkparams with pire0 := (Mk_S1PIRType w__107) } : S1TTWParams)
            (pure (walkparams)))
        else (pure (walkparams)))
    else (pure (walkparams)) ) : SailM S1TTWParams )
  let w__108 ← (( do (HavePAN3Ext ()) ) : SailM Bool )
  let walkparams ← (( do
    if (w__108 : Bool)
    then
      (do
        let w__110 ← (( do
          if ((walkparams.pie == 0#1) : Bool)
          then
            (do
              let w__109 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_SCTLR_EL1_Type_EPAN w__109))))
          else (pure (1#1)) ) : SailM (BitVec 1) )
        let walkparams := ({ walkparams with epan := w__110 } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with epan := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__114 ← (( do
    if ((← do
         (pure ((← do
               (HaveTHExt ())) && ((walkparams.d128 == 0#1) : Bool)))) : Bool)
    then
      (do
        (IsTCR2EL1Enabled ()))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__114 : Bool)
    then
      (do
        let w__115 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with pnch := (_get_TCR2_EL1_Type_PnCH w__115) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with pnch := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__119 ← (( do
    if ((← do
         (pure ((← do
               (HaveAccessFlagUpdateForTableExt ())) && ((walkparams.ha == 1#1) : Bool)))) : Bool)
    then
      (do
        (IsTCR2EL1Enabled ()))
    else (pure false) ) : SailM Bool )
  let walkparams ← (( do
    if (w__119 : Bool)
    then
      (do
        let w__120 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
        let walkparams :=
          ({ walkparams with haft := (_get_TCR2_EL1_Type_HAFT w__120) } : S1TTWParams)
        (pure (walkparams)))
    else
      (let walkparams : S1TTWParams := { walkparams with haft := 0#1 }
      (pure (walkparams))) ) : SailM S1TTWParams )
  let w__123 ← (( do
    if ((← do
         (HaveFeatMEC ())) : Bool)
    then
      (do
        (IsSCTLR2EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let w__125 ← (( do
    if (w__123 : Bool)
    then
      (do
        let w__124 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_SCTLR2_EL2_Type_EMEC w__124))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with emec := w__125 } : S1TTWParams)
  (pure (walkparams))


end ArmFull.Functions
