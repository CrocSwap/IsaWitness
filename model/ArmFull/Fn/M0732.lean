import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0036
import ArmFull.Fn.M0042
import ArmFull.Fn.M0048
import ArmFull.Fn.M0049
import ArmFull.Fn.M0053
import ArmFull.Fn.M0066
import ArmFull.Fn.M0074
import ArmFull.Fn.M0079
import ArmFull.Fn.M0081
import ArmFull.Fn.M0082
import ArmFull.Fn.M0092
import ArmFull.Fn.M0137
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0201
import ArmFull.Fn.M0202
import ArmFull.Fn.M0254
import ArmFull.Fn.M0260

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

/-- Type quantifiers: t : Int -/
def CNTHPS_CTL_SysRegWrite32_420a204f985af014 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
  let __CNTKCTL_EL1_EL0PTEN : (BitVec 1) := (_get_CNTKCTL_EL1_Type_EL0PTEN w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do (CNTKCTL_read__1 ()) ) : SailM (BitVec 32) )
  let __CNTKCTL_PL0PTEN : (BitVec 1) := (_get_CNTKCTL_Type_PL0PTEN w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TGE : (BitVec 1) := (_get_HCR_Type_TGE w__4)
  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__5)
  let w__6 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL1PCEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL1PCEN w__6)
  let w__7 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL1PTEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL1PTEN w__7)
  let w__8 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL0PTEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL0PTEN w__8)
  let w__9 ← (( do (CNTHCTL_read ()) ) : SailM (BitVec 32) )
  let __CNTHCTL_PL1PCEN : (BitVec 1) := (_get_CNTHCTL_Type_PL1PCEN w__9)
  let w__10 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__10)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__17 ← (( do
        (pure ((← do
              if ((← do
                   let w__11 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                   (pure (((! w__11) : Bool)))) : Bool)
              then
                (do
                  let w__15 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_E2H w__13) +++ (_get_HCR_EL2_Type_TGE w__14)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  (pure (((! w__15) : Bool))))
              else (pure false)) && ((__CNTKCTL_EL1_EL0PTEN == 0#1) : Bool))) ) : SailM Bool )
      if (w__17 : Bool)
      then
        (do
          let w__21 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__19 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__19) : Bool))))
                  else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__21 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
      else
        (do
          let w__23 ← (( do
            (pure ((← do
                  (ELUsingAArch32 EL1)) && ((__CNTKCTL_PL0PTEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__23 : Bool)
          then
            (do
              let w__27 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__25 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__25) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__27 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__31 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__31 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                  else sailThrow ((Error_Undefined ()))))
          else
            (do
              let w__36 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__33 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                (pure (((! w__33) : Bool))))
                            else (pure false)) && ((__HCR_EL2_E2H == 0#1) : Bool)))) && ((__CNTHCTL_EL2_EL1PCEN == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__36 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__43 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   let w__38 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                   (pure (((! w__38) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__40 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__41 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__40) +++ (_get_HCR_EL2_Type_TGE
                                      w__41)) == 0b10#2) : Bool))))
                          else (pure false)) && ((__CNTHCTL_EL2_EL1PTEN == 0#1) : Bool))) ) : SailM
                    Bool )
                  if (w__43 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__50 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        (EL2Enabled ())) : Bool)
                                   then
                                     (do
                                       let w__45 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                       (pure (((! w__45) : Bool))))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  let w__47 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  let w__48 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  (pure (((((_get_HCR_EL2_Type_E2H w__47) +++ (_get_HCR_EL2_Type_TGE
                                          w__48)) == 0b11#2) : Bool))))
                              else (pure false)) && ((__CNTHCTL_EL2_EL0PTEN == 0#1) : Bool))) ) :
                        SailM Bool )
                      if (w__50 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__54 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__CNTHCTL_PL1PCEN == 0#1) : Bool))) ) :
                            SailM Bool )
                          if (w__54 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__64 ← (( do
                                if ((← do
                                     if ((← do
                                          if ((← do
                                               if ((← do
                                                    (EL2Enabled ())) : Bool)
                                               then
                                                 (do
                                                   let w__56 ← (( do (ELUsingAArch32 EL2) ) :
                                                     SailM Bool )
                                                   (pure (((! w__56) : Bool))))
                                               else (pure false)) : Bool)
                                          then
                                            (do
                                              let w__58 ← (( do readReg HCR_EL2 ) : SailM
                                                (BitVec 64) )
                                              let w__59 ← (( do readReg HCR_EL2 ) : SailM
                                                (BitVec 64) )
                                              (pure (((((_get_HCR_EL2_Type_E2H w__58) +++ (_get_HCR_EL2_Type_TGE
                                                      w__59)) == 0b11#2) : Bool))))
                                          else (pure false)) : Bool)
                                     then
                                       (do
                                         let w__61 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                         (pure ((((_get_SCR_EL3_Type_NS w__61) == 0#1) : Bool))))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_SEL2))
                                else (pure false) ) : SailM Bool )
                              if (w__64 : Bool)
                              then
                                (do
                                  let w__65 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (__set_CNTHPS_CTL_EL2
                                    (Mk_CNTHPS_CTL_EL2_Type (Sail.BitVec.zeroExtend w__65 64))))
                              else
                                (do
                                  let w__73 ← (( do
                                    if ((← do
                                         if ((← do
                                              if ((← do
                                                   (EL2Enabled ())) : Bool)
                                              then
                                                (do
                                                  let w__67 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                    Bool )
                                                  (pure (((! w__67) : Bool))))
                                              else (pure false)) : Bool)
                                         then
                                           (do
                                             let w__69 ← (( do readReg HCR_EL2 ) : SailM
                                               (BitVec 64) )
                                             let w__70 ← (( do readReg HCR_EL2 ) : SailM
                                               (BitVec 64) )
                                             (pure (((((_get_HCR_EL2_Type_E2H w__69) +++ (_get_HCR_EL2_Type_TGE
                                                     w__70)) == 0b11#2) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__72 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                        (pure ((((_get_SCR_EL3_Type_NS w__72) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__73 : Bool)
                                  then
                                    (do
                                      let w__74 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      (__set_CNTHP_CTL_EL2
                                        (Mk_CNTHP_CTL_EL2_Type (Sail.BitVec.zeroExtend w__74 64))))
                                  else
                                    (do
                                      let w__75 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      (__set_CNTP_CTL (Mk_CNTP_CTL_Type w__75)))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__80 ← (( do
            (pure ((← do
                  (pure ((← do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__77 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                            (pure (((! w__77) : Bool))))
                        else (pure false)) && ((__HCR_EL2_E2H == 0#1) : Bool)))) && ((__CNTHCTL_EL2_EL1PCEN == 0#1) : Bool)))
            ) : SailM Bool )
          if (w__80 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__85 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__82 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                (pure (((! w__82) : Bool))))
                            else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool)))) && ((__CNTHCTL_EL2_EL1PTEN == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__85 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__89 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__CNTHCTL_PL1PCEN == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__89 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__91 ← (( do
                        if (((HaveEL EL3) : Bool) : Bool)
                        then
                          (do
                            (ELUsingAArch32 EL3))
                        else (pure false) ) : SailM Bool )
                      if (w__91 : Bool)
                      then
                        (do
                          let w__92 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (__set_CNTP_CTL_NS (Mk_CNTP_CTL_Type w__92)))
                      else
                        (do
                          let w__93 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (__set_CNTP_CTL (Mk_CNTP_CTL_Type w__93)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__95 ← (( do
                if (((HaveEL EL3) : Bool) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__95 : Bool)
              then
                (do
                  let w__96 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (__set_CNTP_CTL_NS (Mk_CNTP_CTL_Type w__96)))
              else
                (do
                  let w__97 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (__set_CNTP_CTL (Mk_CNTP_CTL_Type w__97))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then
                    (do
                      let w__98 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (__set_CNTP_CTL_S (Mk_CNTP_CTL_Type w__98)))
                  else
                    (do
                      let w__99 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (__set_CNTP_CTL_NS (Mk_CNTP_CTL_Type w__99))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHP_TVAL_SysRegWrite32_8e96a3fad1864250 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
  let __CNTKCTL_EL1_EL0PTEN : (BitVec 1) := (_get_CNTKCTL_EL1_Type_EL0PTEN w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do (CNTKCTL_read__1 ()) ) : SailM (BitVec 32) )
  let __CNTKCTL_PL0PTEN : (BitVec 1) := (_get_CNTKCTL_Type_PL0PTEN w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TGE : (BitVec 1) := (_get_HCR_Type_TGE w__4)
  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__5)
  let w__6 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL1PCEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL1PCEN w__6)
  let w__7 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL1PTEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL1PTEN w__7)
  let w__8 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL0PTEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL0PTEN w__8)
  let w__9 ← (( do (CNTHCTL_read ()) ) : SailM (BitVec 32) )
  let __CNTHCTL_PL1PCEN : (BitVec 1) := (_get_CNTHCTL_Type_PL1PCEN w__9)
  let w__10 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_ECVEn : (BitVec 1) := (_get_SCR_EL3_Type_ECVEn w__10)
  let w__11 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_ECV : (BitVec 1) := (_get_CNTHCTL_EL2_Type_ECV w__11)
  let w__12 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__12)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__19 ← (( do
        (pure ((← do
              if ((← do
                   let w__13 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                   (pure (((! w__13) : Bool)))) : Bool)
              then
                (do
                  let w__17 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_E2H w__15) +++ (_get_HCR_EL2_Type_TGE w__16)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  (pure (((! w__17) : Bool))))
              else (pure false)) && ((__CNTKCTL_EL1_EL0PTEN == 0#1) : Bool))) ) : SailM Bool )
      if (w__19 : Bool)
      then
        (do
          let w__23 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__21 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__21) : Bool))))
                  else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__23 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x03#8))))
      else
        (do
          let w__25 ← (( do
            (pure ((← do
                  (ELUsingAArch32 EL1)) && ((__CNTKCTL_PL0PTEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__25 : Bool)
          then
            (do
              let w__29 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__27 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__27) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__29 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__33 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__33 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                  else sailThrow ((Error_Undefined ()))))
          else
            (do
              let w__38 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__35 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                (pure (((! w__35) : Bool))))
                            else (pure false)) && ((__HCR_EL2_E2H == 0#1) : Bool)))) && ((__CNTHCTL_EL2_EL1PCEN == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__38 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__45 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   let w__40 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                   (pure (((! w__40) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__42 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__43 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__42) +++ (_get_HCR_EL2_Type_TGE
                                      w__43)) == 0b10#2) : Bool))))
                          else (pure false)) && ((__CNTHCTL_EL2_EL1PTEN == 0#1) : Bool))) ) : SailM
                    Bool )
                  if (w__45 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__52 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        (EL2Enabled ())) : Bool)
                                   then
                                     (do
                                       let w__47 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                       (pure (((! w__47) : Bool))))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  let w__49 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  let w__50 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  (pure (((((_get_HCR_EL2_Type_E2H w__49) +++ (_get_HCR_EL2_Type_TGE
                                          w__50)) == 0b11#2) : Bool))))
                              else (pure false)) && ((__CNTHCTL_EL2_EL0PTEN == 0#1) : Bool))) ) :
                        SailM Bool )
                      if (w__52 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__56 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__CNTHCTL_PL1PCEN == 0#1) : Bool))) ) :
                            SailM Bool )
                          if (w__56 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__66 ← (( do
                                if ((← do
                                     if ((← do
                                          if ((← do
                                               if ((← do
                                                    (EL2Enabled ())) : Bool)
                                               then
                                                 (do
                                                   let w__58 ← (( do (ELUsingAArch32 EL2) ) :
                                                     SailM Bool )
                                                   (pure (((! w__58) : Bool))))
                                               else (pure false)) : Bool)
                                          then
                                            (do
                                              let w__60 ← (( do readReg HCR_EL2 ) : SailM
                                                (BitVec 64) )
                                              let w__61 ← (( do readReg HCR_EL2 ) : SailM
                                                (BitVec 64) )
                                              (pure (((((_get_HCR_EL2_Type_E2H w__60) +++ (_get_HCR_EL2_Type_TGE
                                                      w__61)) == 0b11#2) : Bool))))
                                          else (pure false)) : Bool)
                                     then
                                       (do
                                         let w__63 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                         (pure ((((_get_SCR_EL3_Type_NS w__63) == 0#1) : Bool))))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_SEL2))
                                else (pure false) ) : SailM Bool )
                              if (w__66 : Bool)
                              then
                                (do
                                  let w__67 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  let w__68 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                                  writeReg CNTHPS_CVAL_EL2 (Mk_CNTHPS_CVAL_EL2_Type
                                    ((Sail.BitVec.castWidth (m := 64) (sign_extend w__67 64)) + w__68)))
                              else
                                (do
                                  let w__76 ← (( do
                                    if ((← do
                                         if ((← do
                                              if ((← do
                                                   (EL2Enabled ())) : Bool)
                                              then
                                                (do
                                                  let w__70 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                    Bool )
                                                  (pure (((! w__70) : Bool))))
                                              else (pure false)) : Bool)
                                         then
                                           (do
                                             let w__72 ← (( do readReg HCR_EL2 ) : SailM
                                               (BitVec 64) )
                                             let w__73 ← (( do readReg HCR_EL2 ) : SailM
                                               (BitVec 64) )
                                             (pure (((((_get_HCR_EL2_Type_E2H w__72) +++ (_get_HCR_EL2_Type_TGE
                                                     w__73)) == 0b11#2) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__75 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                        (pure ((((_get_SCR_EL3_Type_NS w__75) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__76 : Bool)
                                  then
                                    (do
                                      let w__77 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      let w__78 ← (( do (PhysicalCountInt ()) ) : SailM
                                        (BitVec 64) )
                                      writeReg CNTHP_CVAL_EL2 (Mk_CNTHP_CVAL_EL2_Type
                                        ((Sail.BitVec.castWidth (m := 64) (sign_extend w__77 64)) + w__78)))
                                  else
                                    (do
                                      let w__88 ← (( do
                                        if ((← do
                                             (pure ((← do
                                                   (pure ((← do
                                                         if ((← do
                                                              if ((← do
                                                                   (IsFeatureImplemented FEAT_ECV)) : Bool)
                                                              then
                                                                (do
                                                                  (EL2Enabled ()))
                                                              else (pure false)) : Bool)
                                                         then
                                                           (do
                                                             let w__82 ← (( do
                                                               (ELUsingAArch32 EL2) ) : SailM Bool )
                                                             (pure (((! w__82) : Bool))))
                                                         else (pure false)) && ((__SCR_EL3_ECVEn == 1#1) : Bool)))) && ((__CNTHCTL_EL2_ECV == 1#1) : Bool)))) : Bool)
                                        then
                                          (do
                                            let w__86 ← (( do readReg HCR_EL2 ) : SailM
                                              (BitVec 64) )
                                            let w__87 ← (( do readReg HCR_EL2 ) : SailM
                                              (BitVec 64) )
                                            (pure (((((_get_HCR_EL2_Type_E2H w__86) +++ (_get_HCR_EL2_Type_TGE
                                                    w__87)) != 0b11#2) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__88 : Bool)
                                      then
                                        (do
                                          let w__89 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                          let w__90 ← (( do (PhysicalCountInt ()) ) : SailM
                                            (BitVec 64) )
                                          let w__91 ← (( do readReg CNTPOFF_EL2 ) : SailM
                                            (BitVec 64) )
                                          (CNTP_CVAL_write
                                            (Mk_CNTP_CVAL_Type
                                              ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (sign_extend
                                                    w__89 64)) + w__90)) - w__91))))
                                      else
                                        (do
                                          let w__93 ← (( do
                                            if (((HaveEL EL3) : Bool) : Bool)
                                            then
                                              (do
                                                (ELUsingAArch32 EL3))
                                            else (pure false) ) : SailM Bool )
                                          if (w__93 : Bool)
                                          then
                                            (do
                                              if ((__SCR_NS == 1#1) : Bool)
                                              then
                                                (do
                                                  let w__94 ← (( do (R_read t) ) : SailM
                                                    (BitVec 32) )
                                                  let w__95 ← (( do (PhysicalCountInt ()) ) :
                                                    SailM (BitVec 64) )
                                                  (CNTP_CVAL_NS_write
                                                    (Mk_CNTP_CVAL_Type
                                                      ((Sail.BitVec.castWidth (m := 64) (sign_extend
                                                          w__94 64)) + w__95))))
                                              else
                                                (do
                                                  let w__96 ← (( do (R_read t) ) : SailM
                                                    (BitVec 32) )
                                                  let w__97 ← (( do (PhysicalCountInt ()) ) :
                                                    SailM (BitVec 64) )
                                                  writeReg CNTP_CVAL_S (Mk_CNTP_CVAL_Type
                                                    ((Sail.BitVec.castWidth (m := 64) (sign_extend
                                                        w__96 64)) + w__97))))
                                          else
                                            (do
                                              let w__98 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                              let w__99 ← (( do (PhysicalCountInt ()) ) : SailM
                                                (BitVec 64) )
                                              (CNTP_CVAL_write
                                                (Mk_CNTP_CVAL_Type
                                                  ((Sail.BitVec.castWidth (m := 64) (sign_extend
                                                      w__98 64)) + w__99))))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__104 ← (( do
            (pure ((← do
                  (pure ((← do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__101 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                            (pure (((! w__101) : Bool))))
                        else (pure false)) && ((__HCR_EL2_E2H == 0#1) : Bool)))) && ((__CNTHCTL_EL2_EL1PCEN == 0#1) : Bool)))
            ) : SailM Bool )
          if (w__104 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__109 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__106 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                (pure (((! w__106) : Bool))))
                            else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool)))) && ((__CNTHCTL_EL2_EL1PTEN == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__109 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__113 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__CNTHCTL_PL1PCEN == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__113 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__120 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    if ((← do
                                         if ((← do
                                              (IsFeatureImplemented FEAT_ECV)) : Bool)
                                         then
                                           (do
                                             (EL2Enabled ()))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__117 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                        (pure (((! w__117) : Bool))))
                                    else (pure false)) && ((__SCR_EL3_ECVEn == 1#1) : Bool)))) && ((__CNTHCTL_EL2_ECV == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__120 : Bool)
                      then
                        (do
                          let w__121 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          let w__122 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          let w__123 ← (( do readReg CNTPOFF_EL2 ) : SailM (BitVec 64) )
                          (CNTP_CVAL_write
                            (Mk_CNTP_CVAL_Type
                              ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (sign_extend
                                    w__121 64)) + w__122)) - w__123))))
                      else
                        (do
                          let w__125 ← (( do
                            if (((HaveEL EL3) : Bool) : Bool)
                            then
                              (do
                                (ELUsingAArch32 EL3))
                            else (pure false) ) : SailM Bool )
                          if (w__125 : Bool)
                          then
                            (do
                              let w__126 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              let w__127 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                              (CNTP_CVAL_NS_write
                                (Mk_CNTP_CVAL_Type
                                  ((Sail.BitVec.castWidth (m := 64) (sign_extend w__126 64)) + w__127))))
                          else
                            (do
                              let w__128 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              let w__129 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                              (CNTP_CVAL_write
                                (Mk_CNTP_CVAL_Type
                                  ((Sail.BitVec.castWidth (m := 64) (sign_extend w__128 64)) + w__129)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__131 ← (( do
                if (((HaveEL EL3) : Bool) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__131 : Bool)
              then
                (do
                  let w__132 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  let w__133 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  (CNTP_CVAL_NS_write
                    (Mk_CNTP_CVAL_Type
                      ((Sail.BitVec.castWidth (m := 64) (sign_extend w__132 64)) + w__133))))
              else
                (do
                  let w__134 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  let w__135 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  (CNTP_CVAL_write
                    (Mk_CNTP_CVAL_Type
                      ((Sail.BitVec.castWidth (m := 64) (sign_extend w__134 64)) + w__135)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then
                    (do
                      let w__136 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      let w__137 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      writeReg CNTP_CVAL_S (Mk_CNTP_CVAL_Type
                        ((Sail.BitVec.castWidth (m := 64) (sign_extend w__136 64)) + w__137)))
                  else
                    (do
                      let w__138 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      let w__139 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      (CNTP_CVAL_NS_write
                        (Mk_CNTP_CVAL_Type
                          ((Sail.BitVec.castWidth (m := 64) (sign_extend w__138 64)) + w__139)))))
              else (pure (())))))


end ArmFull.Functions
