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
import ArmFull.Fn.M0020
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0036
import ArmFull.Fn.M0038
import ArmFull.Fn.M0039
import ArmFull.Fn.M0040
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0046
import ArmFull.Fn.M0050
import ArmFull.Fn.M0056
import ArmFull.Fn.M0057
import ArmFull.Fn.M0059
import ArmFull.Fn.M0062
import ArmFull.Fn.M0092
import ArmFull.Fn.M0098
import ArmFull.Fn.M0117
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0158
import ArmFull.Fn.M0166
import ArmFull.Fn.M0174
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0186
import ArmFull.Fn.M0194
import ArmFull.Fn.M0195
import ArmFull.Fn.M0196
import ArmFull.Fn.M0197
import ArmFull.Fn.M0200

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

def SSAdvance (_ : Unit) : SailM Unit := do
  let target ← (( do (DebugTarget ()) ) : SailM (BitVec 2) )
  let step_enabled ← (( do
    if ((← do
         let w__0 ← (( do (ELUsingAArch32 target) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
        (pure ((((_get_MDSCR_EL1_Type_SS w__1) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let active_not_pending ← (( do
    if (step_enabled : Bool)
    then
      (do
        let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__2.SS == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (active_not_pending : Bool)
  then
    (do
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with SS := 0#1 })
  else (pure (()))


def AArch64_IncrementCycleCounter (_ : Unit) : SailM Unit := do
  let w__7 ← (( do
    if ((← do
         (CountPMUEvents CYCLE_COUNTER_ID)) : Bool)
    then
      (do
        if ((← do
             if ((← do
                  if (((! (HaveAArch32 ())) : Bool) : Bool)
                  then (pure true)
                  else
                    (do
                      let w__1 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
                      (pure ((((_get_PMCR_EL0_Type_LC w__1) == 1#1) : Bool))))) : Bool)
             then (pure true)
             else
               (do
                 let w__3 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
                 (pure ((((_get_PMCR_EL0_Type_D w__3) == 0#1) : Bool))))) : Bool)
        then (pure true)
        else
          (do
            (HasElapsed64Cycles ())))
    else (pure false) ) : SailM Bool )
  if (w__7 : Bool)
  then
    (do
      let w__8 ← (( do readReg PMCCNTR_EL0 ) : SailM (BitVec 64) )
      let old_value : Int := (BitVec.toNat w__8)
      let new_value : Int := (old_value +i 1)
      writeReg PMCCNTR_EL0 (Mk_PMCCNTR_EL0_Type (integer_subrange new_value 63 0))
      let ovflw : Int := 32
      let ovflw ← (( do
        if ((HaveAArch32 ()) : Bool)
        then
          (do
            let w__9 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
            let w__10 : Int :=
              if (((_get_PMCR_EL0_Type_LC w__9) == 1#1) : Bool)
              then 64
              else 32
            (pure ((w__10 : Int))))
        else (pure (64)) ) : SailM Int )
      let ovflw : Int := ovflw
      if (((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((64 : Int) -i (ovflw : Int)) +i (1 : Int)))) (integer_subrange
             old_value 64 ovflw)) != (Sail.BitVec.castWidth (integer_subrange new_value 64 ovflw))) : Bool)
      then
        (do
          let w__11 ← (( do readReg PMOVSSET_EL0 ) : SailM (BitVec 64) )
          writeReg PMOVSSET_EL0 (Sail.BitVec.updateSubrange w__11 31 31 1#1)
          let w__12 ← (( do readReg PMOVSCLR_EL0 ) : SailM (BitVec 64) )
          writeReg PMOVSCLR_EL0 (Sail.BitVec.updateSubrange w__12 31 31 1#1))
      else (pure (())))
  else (pure (()))


def CollectContextIDR1 (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (StatisticalProfilingEnabled ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__1.EL == EL2) : Bool)
      then (pure (false))
      else
        (do
          let w__4 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_HCR_EL2_Type_TGE w__3) == 1#1) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__4 : Bool)
          then (pure (false))
          else
            (do
              let w__5 ← (( do readReg PMSCR_EL1 ) : SailM (BitVec 64) )
              (pure (((_get_PMSCR_EL1_Type_CX w__5) == 1#1))))))


def CollectContextIDR2 (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (StatisticalProfilingEnabled ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let w__1 ← (( do (EL2Enabled ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then (pure (false))
      else
        (do
          let w__2 ← (( do readReg PMSCR_EL2 ) : SailM (BitVec 64) )
          (pure (((_get_PMSCR_EL2_Type_CX w__2) == 1#1)))))


def CollectTimeStamp (_ : Unit) : SailM TimeStamp := SailME.run do
  let owning_el ← (( do (undefined_bitvector_at (.site 2426) 2) ) : SailME TimeStamp (BitVec 2) )
  let w__0 ← (( do (StatisticalProfilingEnabled ()) ) : SailME TimeStamp Bool )
  if ((! w__0) : Bool)
  then (pure (TimeStamp_None))
  else
    (do
      let (_, __tup_1) ← (( do (ProfilingBufferOwner ()) ) : SailME TimeStamp
        (SecurityState × (BitVec 2)) )
      let owning_el : (BitVec 2) := __tup_1
      if ((owning_el == EL2) : Bool)
      then
        (do
          let w__1 ← (( do readReg PMSCR_EL2 ) : SailME TimeStamp (BitVec 64) )
          if (((_get_PMSCR_EL2_Type_TS w__1) == 0#1) : Bool)
          then
            (do
              SailME.throw (TimeStamp_None : TimeStamp))
          else (pure (())))
      else
        (do
          let w__2 ← (( do readReg PMSCR_EL1 ) : SailME TimeStamp (BitVec 64) )
          if (((_get_PMSCR_EL1_Type_TS w__2) == 0#1) : Bool)
          then
            (do
              SailME.throw (TimeStamp_None : TimeStamp))
          else (pure (())))
      let PCT_el1 ← (( do (undefined_bitvector_at (.site 2427) 2) ) : SailME TimeStamp (BitVec 2)
        )
      let w__3 ← (( do (HaveECVExt ()) ) : SailME TimeStamp Bool )
      let PCT_el1 ← (( do
        if ((! w__3) : Bool)
        then
          (do
            let w__4 ← (( do readReg PMSCR_EL1 ) : SailME TimeStamp (BitVec 64) )
            let PCT_el1 :=
              ((0#1 +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                    (_get_PMSCR_EL1_Type_PCT w__4) 0)]))) : (BitVec 2))
            (pure (PCT_el1)))
        else
          (do
            let w__5 ← (( do readReg PMSCR_EL1 ) : SailME TimeStamp (BitVec 64) )
            let PCT_el1 := ((_get_PMSCR_EL1_Type_PCT w__5) : (BitVec 2))
            if ((PCT_el1 == 0b10#2) : Bool)
            then
              (do
                let (_, __tup_1) ← (( do (ConstrainUnpredictableBits Unpredictable_PMSCR_PCT 2) )
                  : SailME TimeStamp (Constraint × (BitVec 2)) )
                (pure (__tup_1)))
            else (pure (PCT_el1))) ) : SailME TimeStamp (BitVec 2) )
      let w__6 ← (( do (EL2Enabled ()) ) : SailME TimeStamp Bool )
      if (w__6 : Bool)
      then
        (do
          let PCT_el2 ← (( do (undefined_bitvector_at (.site 2428) 2) ) : SailME TimeStamp
            (BitVec 2) )
          let w__7 ← (( do (HaveECVExt ()) ) : SailME TimeStamp Bool )
          let PCT_el2 ← (( do
            if ((! w__7) : Bool)
            then
              (do
                let w__8 ← (( do readReg PMSCR_EL2 ) : SailME TimeStamp (BitVec 64) )
                let PCT_el2 :=
                  ((0#1 +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                        (_get_PMSCR_EL2_Type_PCT w__8) 0)]))) : (BitVec 2))
                (pure (PCT_el2)))
            else
              (do
                let w__9 ← (( do readReg PMSCR_EL2 ) : SailME TimeStamp (BitVec 64) )
                let PCT_el2 := ((_get_PMSCR_EL2_Type_PCT w__9) : (BitVec 2))
                if ((PCT_el2 == 0b10#2) : Bool)
                then
                  (do
                    let (_, __tup_1) ← (( do
                      (ConstrainUnpredictableBits Unpredictable_PMSCR_PCT 2) ) : SailME TimeStamp
                      (Constraint × (BitVec 2)) )
                    (pure (__tup_1)))
                else (pure (PCT_el2))) ) : SailME TimeStamp (BitVec 2) )
          match PCT_el2 with
          | 0b00 =>
            (do
              let w__10 ← (( do (IsInHost ()) ) : SailME TimeStamp Bool )
              let w__11 : TimeStamp :=
                if (w__10 : Bool)
                then TimeStamp_Physical
                else TimeStamp_Virtual
              SailME.throw (w__11 : TimeStamp))
          | 0b01 =>
            (do
              if ((owning_el == EL2) : Bool)
              then
                (do
                  SailME.throw (TimeStamp_Physical : TimeStamp))
              else (pure (())))
          | 0b11 =>
            (do
              let w__12 ← (( do (HaveECVExt ()) ) : SailME TimeStamp Bool )
              ArmFull.assert w__12 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:34626.33-34626.34"
              let w__15 ← (( do
                if (((owning_el == EL1) && (PCT_el1 == 0b00#2)) : Bool)
                then
                  (do
                    let w__13 ← (( do (IsInHost ()) ) : SailME TimeStamp Bool )
                    let w__14 : TimeStamp :=
                      if (w__13 : Bool)
                      then TimeStamp_Physical
                      else TimeStamp_Virtual
                    (pure (w__14)))
                else (pure (TimeStamp_OffsetPhysical)) ) : SailME TimeStamp TimeStamp )
              SailME.throw (w__15 : TimeStamp))
          | _ =>
            (do
              (Unreachable ())))
      else (pure (()))
      match PCT_el1 with
      | 0b00 =>
        (do
          let w__16 ← (( do (IsInHost ()) ) : SailME TimeStamp Bool )
          let w__17 : TimeStamp :=
            if (w__16 : Bool)
            then TimeStamp_Physical
            else TimeStamp_Virtual
          (pure (w__17)))
      | 0b01 => (pure (TimeStamp_Physical))
      | 0b11 =>
        (do
          let w__18 ← (( do (HaveECVExt ()) ) : SailME TimeStamp Bool )
          ArmFull.assert w__18 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:34647.29-34647.30"
          (pure (TimeStamp_OffsetPhysical)))
      | _ =>
        (do
          (Unreachable ())
          (undefined_TimeStamp (.site 2429) ())))


def MAIR0_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _MAIR0_NS ) : SailM MAIR0_Type )
  let w__0 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (PRRR_NS_read ()) ) : SailM (BitVec 32) )
      let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__1 0 32)) : (BitVec 32))
      (pure (r)))
  else
    (do
      let w__3 ← (( do
        if (((! (HaveEL EL3)) : Bool) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
            (pure (((! w__2) : Bool)))) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          let w__4 ← (( do readReg MAIR_EL1 ) : SailM (BitVec 64) )
          let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__4 0 32)) : (BitVec 32))
          (pure (r)))
      else
        (do
          let w__5 ← (( do (PRRR_read ()) ) : SailM (BitVec 32) )
          let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__5 0 32)) : (BitVec 32))
          (pure (r))))


def MAIR1_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _MAIR1_NS ) : SailM MAIR1_Type )
  let w__0 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (NMRR_NS_read ()) ) : SailM (BitVec 32) )
      let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__1 0 32)) : (BitVec 32))
      (pure (r)))
  else
    (do
      let w__3 ← (( do
        if (((! (HaveEL EL3)) : Bool) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
            (pure (((! w__2) : Bool)))) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          let w__4 ← (( do readReg MAIR_EL1 ) : SailM (BitVec 64) )
          let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__4 32 32)) : (BitVec 32))
          (pure (r)))
      else
        (do
          let w__5 ← (( do (NMRR_read ()) ) : SailM (BitVec 32) )
          let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__5 0 32)) : (BitVec 32))
          (pure (r))))


def AArch32_S1DCacheEnabled (regime : Regime) : SailM Bool := do
  match regime with
  | .Regime_EL30 =>
    (do
      let w__0 ← (( do readReg SCTLR_S ) : SailM (BitVec 32) )
      (pure (((_get_SCTLR_Type_C w__0) == 1#1))))
  | .Regime_EL2 =>
    (do
      let w__1 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
      (pure (((_get_HSCTLR_Type_C w__1) == 1#1))))
  | .Regime_EL10 =>
    (do
      let w__4 ← (( do
        if ((HaveAArch32EL EL3) : Bool)
        then
          (do
            let w__2 ← (( do (SCTLR_NS_read ()) ) : SailM (BitVec 32) )
            (pure ((_get_SCTLR_Type_C w__2))))
        else
          (do
            let w__3 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
            (pure ((_get_SCTLR_Type_C w__3)))) ) : SailM (BitVec 1) )
      (pure ((w__4 == 1#1))))
  | _ =>
    (do
      (undefined_bool_at (← occLabel 2508) ()))


def AArch32_S1ICacheEnabled (regime : Regime) : SailM Bool := do
  match regime with
  | .Regime_EL30 =>
    (do
      let w__0 ← (( do readReg SCTLR_S ) : SailM (BitVec 32) )
      (pure (((_get_SCTLR_Type_I w__0) == 1#1))))
  | .Regime_EL2 =>
    (do
      let w__1 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
      (pure (((_get_HSCTLR_Type_I w__1) == 1#1))))
  | .Regime_EL10 =>
    (do
      let w__4 ← (( do
        if ((HaveAArch32EL EL3) : Bool)
        then
          (do
            let w__2 ← (( do (SCTLR_NS_read ()) ) : SailM (BitVec 32) )
            (pure ((_get_SCTLR_Type_I w__2))))
        else
          (do
            let w__3 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
            (pure ((_get_SCTLR_Type_I w__3)))) ) : SailM (BitVec 1) )
      (pure ((w__4 == 1#1))))
  | _ =>
    (do
      (undefined_bool_at (← occLabel 2509) ()))


def AArch32_S1Enabled (regime : Regime) (ss : SecurityState) : SailM Bool := do
  if ((BEq.beq regime Regime_EL2) : Bool)
  then
    (do
      let w__0 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
      (pure (((_get_HSCTLR_Type_M w__0) == 1#1))))
  else
    (do
      if ((BEq.beq regime Regime_EL30) : Bool)
      then
        (do
          let w__1 ← (( do readReg SCTLR_S ) : SailM (BitVec 32) )
          (pure (((_get_SCTLR_Type_M w__1) == 1#1))))
      else
        (do
          let w__2 ← (( do (AArch32_EL2Enabled ss) ) : SailM Bool )
          if ((! w__2) : Bool)
          then
            (do
              let w__5 ← (( do
                if ((HaveAArch32EL EL3) : Bool)
                then
                  (do
                    let w__3 ← (( do (SCTLR_NS_read ()) ) : SailM (BitVec 32) )
                    (pure ((_get_SCTLR_Type_M w__3))))
                else
                  (do
                    let w__4 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
                    (pure ((_get_SCTLR_Type_M w__4)))) ) : SailM (BitVec 1) )
              (pure ((w__5 == 1#1))))
          else
            (do
              let w__6 ← (( do (ELStateUsingAArch32 EL2 (BEq.beq ss SS_Secure)) ) : SailM Bool )
              if (w__6 : Bool)
              then
                (do
                  if ((← do
                       let w__7 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                       let w__8 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                       (pure (((((_get_HCR_Type_TGE w__7) +++ (_get_HCR_Type_DC w__8)) == 0b00#2) : Bool)))) : Bool)
                  then
                    (do
                      let w__11 ← (( do
                        if ((HaveAArch32EL EL3) : Bool)
                        then
                          (do
                            let w__9 ← (( do (SCTLR_NS_read ()) ) : SailM (BitVec 32) )
                            (pure ((_get_SCTLR_Type_M w__9))))
                        else
                          (do
                            let w__10 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
                            (pure ((_get_SCTLR_Type_M w__10)))) ) : SailM (BitVec 1) )
                      (pure (((w__11 == 1#1) : Bool))))
                  else (pure false))
              else
                (do
                  if ((← do
                       let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                       let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                       (pure (((((_get_HCR_EL2_Type_TGE w__13) +++ (_get_HCR_EL2_Type_DC w__14)) == 0b00#2) : Bool)))) : Bool)
                  then
                    (do
                      let w__15 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
                      (pure ((((_get_SCTLR_Type_M w__15) == 1#1) : Bool))))
                  else (pure false)))))


def AArch32_TLBContextEL10 (ss : SecurityState) (va : (BitVec 32)) : SailM TLBContext := do
  let tlbcontext ← (( do (undefined_TLBContext (← occLabel 2527) ()) ) : SailM TLBContext )
  let ttbcr ← (( do (undefined_TTBCR_Type (← occLabel 2528) ()) ) : SailM TTBCR_Type )
  let ttbr0 ← (( do (undefined_TTBR0_Type (← occLabel 2529) ()) ) : SailM TTBR0_Type )
  let ttbr1 ← (( do (undefined_TTBR1_Type (← occLabel 2530) ()) ) : SailM TTBR1_Type )
  let contextidr ← (( do (undefined_CONTEXTIDR_Type (← occLabel 2531) ()) ) : SailM
    CONTEXTIDR_Type )
  let (contextidr, ttbcr, ttbr0, ttbr1) ← (( do
    if ((HaveAArch32EL EL3) : Bool)
    then
      (do
        let w__0 ← (( do (TTBCR_NS_read ()) ) : SailM (BitVec 32) )
        let ttbcr := (w__0 : (BitVec 32))
        let w__1 ← (( do readReg TTBR0_NS ) : SailM (BitVec 64) )
        let ttbr0 := (w__1 : (BitVec 64))
        let w__2 ← (( do readReg TTBR1_NS ) : SailM (BitVec 64) )
        let ttbr1 := (w__2 : (BitVec 64))
        let w__3 ← (( do (CONTEXTIDR_NS_read ()) ) : SailM (BitVec 32) )
        let contextidr := (w__3 : (BitVec 32))
        (pure ((contextidr, ttbcr, ttbr0, ttbr1))))
    else
      (do
        let w__4 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
        let ttbcr := (w__4 : (BitVec 32))
        let w__5 ← (( do (TTBR0_read ()) ) : SailM (BitVec 64) )
        let ttbr0 := (w__5 : (BitVec 64))
        let w__6 ← (( do (TTBR1_read ()) ) : SailM (BitVec 64) )
        let ttbr1 := (w__6 : (BitVec 64))
        let w__7 ← (( do (CONTEXTIDR_read ()) ) : SailM (BitVec 32) )
        let contextidr := (w__7 : (BitVec 32))
        (pure ((contextidr, ttbcr, ttbr0, ttbr1)))) ) : SailM
    ((BitVec 32) × (BitVec 32) × (BitVec 64) × (BitVec 64)) )
  let tlbcontext : TLBContext := { tlbcontext with ss := ss }
  let tlbcontext : TLBContext := { tlbcontext with regime := Regime_EL10 }
  let w__8 ← (( do (AArch32_EL2Enabled ss) ) : SailM Bool )
  let tlbcontext ← (( do
    if (w__8 : Bool)
    then
      (do
        let w__9 ← (( do readReg VTTBR ) : SailM (BitVec 64) )
        let tlbcontext :=
          ({ tlbcontext with vmid := (Sail.BitVec.zeroExtend (_get_VTTBR_Type_VMID w__9) 16) } : TLBContext)
        (pure (tlbcontext)))
    else (pure (tlbcontext)) ) : SailM TLBContext )
  let tlbcontext : TLBContext :=
    if (((_get_TTBCR_Type_EAE ttbcr) == 1#1) : Bool)
    then
      { tlbcontext with asid := (Sail.BitVec.zeroExtend
          (if (((_get_TTBCR_Type_A1 ttbcr) == 0#1) : Bool)
          then (_get_TTBR0_Type_ASID ttbr0)
          else (_get_TTBR1_Type_ASID ttbr1)) 16) }
    else
      { tlbcontext with asid := (Sail.BitVec.zeroExtend (_get_CONTEXTIDR_Type_ASID contextidr) 16) }
  let tlbcontext : TLBContext := { tlbcontext with tg := TGx_4KB }
  let tlbcontext : TLBContext := { tlbcontext with ia := (Sail.BitVec.zeroExtend va 64) }
  let w__11 ← (( do
    (pure ((← do
          (HaveCommonNotPrivateTransExt ())) && (((_get_TTBCR_Type_EAE ttbcr) == 1#1) : Bool))) ) :
    SailM Bool )
  if (w__11 : Bool)
  then
    (do
      let w__12 ← (( do
        (AArch32_GetVARange va (_get_TTBCR_Type_T0SZ ttbcr) (_get_TTBCR_Type_T1SZ ttbcr)) ) : SailM
        VARange )
      let tlbcontext : TLBContext :=
        if ((BEq.beq w__12 VARange_LOWER) : Bool)
        then { tlbcontext with cnp := (_get_TTBR0_Type_CnP ttbr0) }
        else { tlbcontext with cnp := (_get_TTBR1_Type_CnP ttbr1) }
      (pure (tlbcontext)))
  else
    (let tlbcontext : TLBContext := { tlbcontext with cnp := 0#1 }
    (pure (tlbcontext)))


def AArch32_OutputDomain (regime : Regime) (domain : (BitVec 4)) : SailM (BitVec 2) := do
  let Dn ← (( do (undefined_bitvector_at (← occLabel 2580) 2) ) : SailM (BitVec 2) )
  let index : Int := (2 *i (BitVec.toNat domain))
  let Dn ← (( do
    if ((BEq.beq regime Regime_EL30) : Bool)
    then
      (do
        let w__0 ← (( do readReg DACR_S ) : SailM (BitVec 32) )
        let Dn :=
          ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__0
            (Sail.Int.toNatChecked ((index +i 1))) (Sail.Int.toNatChecked (index)))) : (BitVec 2))
        (pure (Dn)))
    else
      (do
        if ((HaveAArch32EL EL3) : Bool)
        then
          (do
            let w__1 ← (( do (DACR_NS_read ()) ) : SailM (BitVec 32) )
            let Dn :=
              ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__1
                (Sail.Int.toNatChecked ((index +i 1))) (Sail.Int.toNatChecked (index)))) : (BitVec 2))
            (pure (Dn)))
        else
          (do
            let w__2 ← (( do (DACR_read ()) ) : SailM (BitVec 32) )
            let Dn :=
              ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__2
                (Sail.Int.toNatChecked ((index +i 1))) (Sail.Int.toNatChecked (index)))) : (BitVec 2))
            (pure (Dn)))) ) : SailM (BitVec 2) )
  if ((Dn == 0b10#2) : Bool)
  then
    (do
      let (_, __tup_1) ← (( do (ConstrainUnpredictableBits Unpredictable_RESDACR 2) ) : SailM
        (Constraint × (BitVec 2)) )
      (pure (__tup_1)))
  else (pure (Dn))


def AArch32_S1SDHasPermissionsFault (regime : Regime) (perms_in : Permissions) (memtype : MemType) (paspace : PASpace) (accdesc : AccessDescriptor) : SailM Bool := do
  let pan ← (( do (undefined_bitvector_at (← occLabel 2581) 1) ) : SailM (BitVec 1) )
  let r ← (( do (undefined_bitvector_at (← occLabel 2582) 1) ) : SailM (BitVec 1) )
  let w ← (( do (undefined_bitvector_at (← occLabel 2583) 1) ) : SailM (BitVec 1) )
  let x ← (( do (undefined_bitvector_at (← occLabel 2584) 1) ) : SailM (BitVec 1) )
  let perms : Permissions := perms_in
  let pr ← (( do (undefined_bitvector_at (← occLabel 2585) 1) ) : SailM (BitVec 1) )
  let pw ← (( do (undefined_bitvector_at (← occLabel 2586) 1) ) : SailM (BitVec 1) )
  let ur ← (( do (undefined_bitvector_at (← occLabel 2587) 1) ) : SailM (BitVec 1) )
  let uw ← (( do (undefined_bitvector_at (← occLabel 2588) 1) ) : SailM (BitVec 1) )
  let sctlr ← (( do (undefined_SCTLR_Type (← occLabel 2589) ()) ) : SailM SCTLR_Type )
  let sctlr ← (( do
    if ((BEq.beq regime Regime_EL30) : Bool)
    then
      (do
        readReg SCTLR_S)
    else
      (do
        if ((HaveAArch32EL EL3) : Bool)
        then
          (do
            (SCTLR_NS_read ()))
        else
          (do
            (SCTLR_read__2 ()))) ) : SailM (BitVec 32) )
  let (perms, pr, pw, ur, uw) ← (( do
    if (((_get_SCTLR_Type_AFE sctlr) == 0#1) : Bool)
    then
      (do
        let perms ← (( do
          if ((perms.ap == 0b100#3) : Bool)
          then
            (do
              let w__3 ← (( do (__IMPDEF_bits 3 "Reserved short descriptor AP encoding") ) : SailM
                (BitVec 3) )
              let perms := ({ perms with ap := w__3 } : Permissions)
              (pure (perms)))
          else (pure (perms)) ) : SailM Permissions )
        let (pr, pw, ur, uw) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)) :=
          match perms.ap with
          | 0b000 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((0#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let ur : (BitVec 1) := tup__2
            let uw : (BitVec 1) := tup__3
            (pr, pw, ur, uw))
          | 0b001 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 1#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let ur : (BitVec 1) := tup__2
            let uw : (BitVec 1) := tup__3
            (pr, pw, ur, uw))
          | 0b010 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 1#1, 1#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let ur : (BitVec 1) := tup__2
            let uw : (BitVec 1) := tup__3
            (pr, pw, ur, uw))
          | 0b011 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 1#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let ur : (BitVec 1) := tup__2
            let uw : (BitVec 1) := tup__3
            (pr, pw, ur, uw))
          | 0b101 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let ur : (BitVec 1) := tup__2
            let uw : (BitVec 1) := tup__3
            (pr, pw, ur, uw))
          | 0b110 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 0#1, 1#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let ur : (BitVec 1) := tup__2
            let uw : (BitVec 1) := tup__3
            (pr, pw, ur, uw))
          | 0b111 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 0#1, 1#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let ur : (BitVec 1) := tup__2
            let uw : (BitVec 1) := tup__3
            (pr, pw, ur, uw))
          | _ => (pr, pw, ur, uw)
        (pure ((perms, pr, pw, ur, uw))))
    else
      (let (pr, pw, ur, uw) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)) :=
        match (BitVec.setWidth 2 (Sail.BitVec.extractLsb perms.ap 2 1)) with
        | 0b00 =>
          (let (tup__0, tup__1, tup__2, tup__3) :=
            ((1#1, 1#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
          let pr : (BitVec 1) := tup__0
          let pw : (BitVec 1) := tup__1
          let ur : (BitVec 1) := tup__2
          let uw : (BitVec 1) := tup__3
          (pr, pw, ur, uw))
        | 0b01 =>
          (let (tup__0, tup__1, tup__2, tup__3) :=
            ((1#1, 1#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
          let pr : (BitVec 1) := tup__0
          let pw : (BitVec 1) := tup__1
          let ur : (BitVec 1) := tup__2
          let uw : (BitVec 1) := tup__3
          (pr, pw, ur, uw))
        | 0b10 =>
          (let (tup__0, tup__1, tup__2, tup__3) :=
            ((1#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
          let pr : (BitVec 1) := tup__0
          let pw : (BitVec 1) := tup__1
          let ur : (BitVec 1) := tup__2
          let uw : (BitVec 1) := tup__3
          (pr, pw, ur, uw))
        | 0b11 =>
          (let (tup__0, tup__1, tup__2, tup__3) :=
            ((1#1, 0#1, 1#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
          let pr : (BitVec 1) := tup__0
          let pw : (BitVec 1) := tup__1
          let ur : (BitVec 1) := tup__2
          let uw : (BitVec 1) := tup__3
          (pr, pw, ur, uw))
        | _ => (pr, pw, ur, uw)
      (pure ((perms, pr, pw, ur, uw)))) ) : SailM
    (Permissions × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)) )
  let ux : (BitVec 1) :=
    (ur &&& (Complement.complement (perms.xn ||| (uw &&& (_get_SCTLR_Type_WXN sctlr)))))
  let px : (BitVec 1) :=
    (pr &&& (Complement.complement
        (((perms.xn ||| perms.pxn) ||| (pw &&& (_get_SCTLR_Type_WXN sctlr))) ||| (uw &&& (_get_SCTLR_Type_UWXN
              sctlr)))))
  let w__5 ← (( do
    (pure ((← do
          (HavePANExt ())) && (accdesc.pan : Bool))) ) : SailM Bool )
  let (pr, pw) ← (( do
    if (w__5 : Bool)
    then
      (do
        let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
        let pan : (BitVec 1) := (w__6.PAN &&& (ur ||| uw))
        let pr : (BitVec 1) := (pr &&& (Complement.complement pan))
        let pw : (BitVec 1) := (pw &&& (Complement.complement pan))
        (pure ((pr, pw))))
    else (pure ((pr, pw))) ) : SailM ((BitVec 1) × (BitVec 1)) )
  let (tup__0, tup__1, tup__2) :=
    (if ((accdesc.el == EL0) : Bool)
    then (ur, uw, ux)
    else (pr, pw, px) : ((BitVec 1) × (BitVec 1) × (BitVec 1)))
  let r : (BitVec 1) := tup__0
  let w : (BitVec 1) := tup__1
  let x : (BitVec 1) := tup__2
  let x ← (( do
    if (((BEq.beq accdesc.ss SS_Secure) && (BEq.beq paspace PAS_NonSecure)) : Bool)
    then
      (do
        let w__7 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
        let w__10 ← (( do
          if (w__7 : Bool)
          then
            (do
              let w__8 ← (( do readReg SCR ) : SailM (BitVec 32) )
              (pure ((_get_SCR_Type_SIF w__8))))
          else
            (do
              let w__9 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
              (pure ((_get_SCR_EL3_Type_SIF w__9)))) ) : SailM (BitVec 1) )
        let x := ((x &&& (Complement.complement w__10)) : (BitVec 1))
        (pure (x)))
    else (pure (x)) ) : SailM (BitVec 1) )
  let x := x
  if ((BEq.beq accdesc.acctype AccessType_IFETCH) : Bool)
  then
    (do
      let w__12 ← (( do
        if (((BEq.beq memtype MemType_Device) : Bool) : Bool)
        then
          (do
            let w__11 ← (( do (ConstrainUnpredictable Unpredictable_INSTRDEVICE) ) : SailM
              Constraint )
            (pure (((BEq.beq w__11 Constraint_FAULT) : Bool))))
        else (pure false) ) : SailM Bool )
      let w__13 : Bool :=
        if (w__12 : Bool)
        then true
        else (x == 0#1)
      (pure (w__13)))
  else
    (pure (if (((BEq.beq accdesc.acctype AccessType_IC) || (BEq.beq accdesc.acctype AccessType_DC)) : Bool)
      then false
      else
        (if (accdesc.write : Bool)
        then (w == 0#1)
        else (r == 0#1))))


end ArmFull.Functions
