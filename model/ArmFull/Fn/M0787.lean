import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0035
import ArmFull.Fn.M0042
import ArmFull.Fn.M0054
import ArmFull.Fn.M0055
import ArmFull.Fn.M0056
import ArmFull.Fn.M0059
import ArmFull.Fn.M0070
import ArmFull.Fn.M0075
import ArmFull.Fn.M0100
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0199
import ArmFull.Fn.M0202
import ArmFull.Fn.M0254
import ArmFull.Fn.M0255
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
def ICV_CTLR_SysRegWrite32_6f9cee422585c5f5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_M : (BitVec 5) := w__1.M
  let w__2 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T12 : (BitVec 1) := (_get_HSTR_EL2_Type_T12 w__2)
  let w__3 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T12 : (BitVec 1) := (_get_HSTR_Type_T12 w__3)
  let w__4 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  let __ICH_HCR_EL2_TC : (BitVec 1) := (_get_ICH_HCR_EL2_Type_TC w__4)
  let w__5 ← (( do (ICH_HCR_read ()) ) : SailM (BitVec 32) )
  let __ICH_HCR_TC : (BitVec 1) := (_get_ICH_HCR_Type_TC w__5)
  let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_FMO : (BitVec 1) := (_get_HCR_EL2_Type_FMO w__6)
  let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_IMO : (BitVec 1) := (_get_HCR_EL2_Type_IMO w__7)
  let w__8 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_FMO : (BitVec 1) := (_get_HCR_Type_FMO w__8)
  let w__9 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_IMO : (BitVec 1) := (_get_HCR_Type_IMO w__9)
  let w__10 ← (( do (ICC_HSRE_read ()) ) : SailM (BitVec 32) )
  let __ICC_HSRE_SRE : (BitVec 1) := (_get_ICC_HSRE_Type_SRE w__10)
  let w__11 ← (( do readReg ICC_MSRE ) : SailM (BitVec 32) )
  let __ICC_MSRE_SRE : (BitVec 1) := (_get_ICC_MSRE_Type_SRE w__11)
  let w__12 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__12)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__23 ← (( do
            if ((← do
                 if ((← do
                      if ((← do
                           if ((← do
                                (pure ((← do
                                      (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                           then
                             (do
                               let w__15 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                               (pure ((((_get_EDSCR_Type_SDD w__15) == 1#1) : Bool))))
                           else (pure false)) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) : Bool)
                 then
                   (do
                     let w__19 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                     (pure (((! w__19) : Bool))))
                 else (pure false)) : Bool)
            then
              (do
                let w__21 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                let w__22 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                (pure (((((_get_SCR_EL3_Type_IRQ w__21) +++ (_get_SCR_EL3_Type_FIQ w__22)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__23 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__35 ← (( do
                if ((← do
                     (pure ((← do
                           if ((← do
                                if ((← do
                                     if ((← do
                                          (pure ((← do
                                                (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                     then
                                       (do
                                         let w__26 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                         (pure ((((_get_EDSCR_Type_SDD w__26) == 1#1) : Bool))))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                                else (pure false)) : Bool)
                           then
                             (do
                               (ELUsingAArch32 EL3))
                           else (pure false)) && ((__PSTATE_M != M32_Monitor) : Bool)))) : Bool)
                then
                  (do
                    let w__33 ← (( do readReg SCR ) : SailM (BitVec 32) )
                    let w__34 ← (( do readReg SCR ) : SailM (BitVec 32) )
                    (pure (((((_get_SCR_Type_IRQ w__33) +++ (_get_SCR_Type_FIQ w__34)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__35 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__39 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__37 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__37) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T12 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__39 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__43 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HSTR_T12 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__43 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__47 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__45 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                      (pure (((! w__45) : Bool))))
                                  else (pure false)) && ((__ICH_HCR_EL2_TC == 1#1) : Bool))) ) :
                            SailM Bool )
                          if (w__47 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__51 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__ICH_HCR_TC == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__51 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__55 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (EL2Enabled ())) : Bool)
                                          then
                                            (do
                                              let w__53 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                Bool )
                                              (pure (((! w__53) : Bool))))
                                          else (pure false)) && ((__HCR_EL2_FMO == 1#1) : Bool))) )
                                    : SailM Bool )
                                  if (w__55 : Bool)
                                  then
                                    (do
                                      let w__56 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      (ICV_CTLR_write (Mk_ICV_CTLR_Type w__56)))
                                  else
                                    (do
                                      let w__60 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (EL2Enabled ())) : Bool)
                                              then
                                                (do
                                                  let w__58 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                    Bool )
                                                  (pure (((! w__58) : Bool))))
                                              else (pure false)) && ((__HCR_EL2_IMO == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__60 : Bool)
                                      then
                                        (do
                                          let w__61 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                          (ICV_CTLR_write (Mk_ICV_CTLR_Type w__61)))
                                      else
                                        (do
                                          let w__65 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       (EL2Enabled ())) : Bool)
                                                  then
                                                    (do
                                                      (ELUsingAArch32 EL2))
                                                  else (pure false)) && ((__HCR_FMO == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__65 : Bool)
                                          then
                                            (do
                                              let w__66 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                              (ICV_CTLR_write (Mk_ICV_CTLR_Type w__66)))
                                          else
                                            (do
                                              let w__70 ← (( do
                                                (pure ((← do
                                                      if ((← do
                                                           (EL2Enabled ())) : Bool)
                                                      then
                                                        (do
                                                          (ELUsingAArch32 EL2))
                                                      else (pure false)) && ((__HCR_IMO == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__70 : Bool)
                                              then
                                                (do
                                                  let w__71 ← (( do (R_read t) ) : SailM
                                                    (BitVec 32) )
                                                  (ICV_CTLR_write (Mk_ICV_CTLR_Type w__71)))
                                              else
                                                (do
                                                  let w__76 ← (( do
                                                    if ((← do
                                                         if (((HaveEL EL3) : Bool) : Bool)
                                                         then
                                                           (do
                                                             let w__72 ← (( do
                                                               (ELUsingAArch32 EL3) ) : SailM Bool )
                                                             (pure (((! w__72) : Bool))))
                                                         else (pure false)) : Bool)
                                                    then
                                                      (do
                                                        let w__74 ← (( do readReg SCR_EL3 ) :
                                                          SailM (BitVec 64) )
                                                        let w__75 ← (( do readReg SCR_EL3 ) :
                                                          SailM (BitVec 64) )
                                                        (pure (((((_get_SCR_EL3_Type_IRQ w__74) +++ (_get_SCR_EL3_Type_FIQ
                                                                w__75)) == 0b11#2) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__76 : Bool)
                                                  then
                                                    (do
                                                      let w__79 ← (( do
                                                        if ((← do
                                                             (Halted ())) : Bool)
                                                        then
                                                          (do
                                                            let w__78 ← (( do (EDSCR_read ()) ) :
                                                              SailM (BitVec 32) )
                                                            (pure ((((_get_EDSCR_Type_SDD w__78) == 1#1) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__79 : Bool)
                                                      then sailThrow ((Error_Undefined ()))
                                                      else
                                                        (do
                                                          (AArch64_AArch32SystemAccessTrap EL3
                                                            (BitVec.toNat 0x03#8))))
                                                  else
                                                    (do
                                                      let w__85 ← (( do
                                                        if ((← do
                                                             (pure ((← do
                                                                   if (((HaveEL EL3) : Bool) : Bool)
                                                                   then
                                                                     (do
                                                                       (ELUsingAArch32 EL3))
                                                                   else (pure false)) && ((__PSTATE_M != M32_Monitor) : Bool)))) : Bool)
                                                        then
                                                          (do
                                                            let w__83 ← (( do readReg SCR ) :
                                                              SailM (BitVec 32) )
                                                            let w__84 ← (( do readReg SCR ) :
                                                              SailM (BitVec 32) )
                                                            (pure (((((_get_SCR_Type_IRQ w__83) +++ (_get_SCR_Type_FIQ
                                                                    w__84)) == 0b11#2) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__85 : Bool)
                                                      then
                                                        (do
                                                          let w__88 ← (( do
                                                            if ((← do
                                                                 (Halted ())) : Bool)
                                                            then
                                                              (do
                                                                let w__87 ← (( do (EDSCR_read ())
                                                                  ) : SailM (BitVec 32) )
                                                                (pure ((((_get_EDSCR_Type_SDD w__87) == 1#1) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__88 : Bool)
                                                          then sailThrow ((Error_Undefined ()))
                                                          else
                                                            (do
                                                              (AArch32_TakeMonitorTrapException ())))
                                                      else
                                                        (do
                                                          if ((HaveEL EL3) : Bool)
                                                          then
                                                            (do
                                                              let w__89 ← (( do (R_read t) ) :
                                                                SailM (BitVec 32) )
                                                              (ICC_CTLR_NS_write
                                                                (Mk_ICC_CTLR_Type w__89)))
                                                          else
                                                            (do
                                                              let w__90 ← (( do (R_read t) ) :
                                                                SailM (BitVec 32) )
                                                              (ICC_CTLR_write
                                                                (Mk_ICC_CTLR_Type w__90))))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__101 ← (( do
                if ((← do
                     if ((← do
                          if ((← do
                               if ((← do
                                    (pure ((← do
                                          (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                               then
                                 (do
                                   let w__93 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                   (pure ((((_get_EDSCR_Type_SDD w__93) == 1#1) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) : Bool)
                     then
                       (do
                         let w__97 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                         (pure (((! w__97) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__99 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    let w__100 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    (pure (((((_get_SCR_EL3_Type_IRQ w__99) +++ (_get_SCR_EL3_Type_FIQ w__100)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__101 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__112 ← (( do
                    if ((← do
                         if ((← do
                              if ((← do
                                   if ((← do
                                        (pure ((← do
                                              (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                   then
                                     (do
                                       let w__104 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                       (pure ((((_get_EDSCR_Type_SDD w__104) == 1#1) : Bool))))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                              else (pure false)) : Bool)
                         then
                           (do
                             (ELUsingAArch32 EL3))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__110 ← (( do readReg SCR ) : SailM (BitVec 32) )
                        let w__111 ← (( do readReg SCR ) : SailM (BitVec 32) )
                        (pure (((((_get_SCR_Type_IRQ w__110) +++ (_get_SCR_Type_FIQ w__111)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__112 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__ICC_HSRE_SRE == 0#1) : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__117 ← (( do
                            if ((← do
                                 if (((HaveEL EL3) : Bool) : Bool)
                                 then
                                   (do
                                     let w__113 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                     (pure (((! w__113) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__115 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                let w__116 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                (pure (((((_get_SCR_EL3_Type_IRQ w__115) +++ (_get_SCR_EL3_Type_FIQ
                                        w__116)) == 0b11#2) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__117 : Bool)
                          then
                            (do
                              let w__120 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__119 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__119) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__120 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                          else
                            (do
                              let w__125 ← (( do
                                if ((← do
                                     if (((HaveEL EL3) : Bool) : Bool)
                                     then
                                       (do
                                         (ELUsingAArch32 EL3))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__123 ← (( do readReg SCR ) : SailM (BitVec 32) )
                                    let w__124 ← (( do readReg SCR ) : SailM (BitVec 32) )
                                    (pure (((((_get_SCR_Type_IRQ w__123) +++ (_get_SCR_Type_FIQ
                                            w__124)) == 0b11#2) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__125 : Bool)
                              then
                                (do
                                  let w__128 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__127 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__127) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__128 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch32_TakeMonitorTrapException ())))
                              else
                                (do
                                  if ((HaveEL EL3) : Bool)
                                  then
                                    (do
                                      let w__129 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      (ICC_CTLR_NS_write (Mk_ICC_CTLR_Type w__129)))
                                  else
                                    (do
                                      let w__130 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      (ICC_CTLR_write (Mk_ICC_CTLR_Type w__130)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__SCR_NS == 0#1) : Bool)
                      then
                        (do
                          let w__131 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (ICC_CTLR_S_write (Mk_ICC_CTLR_Type w__131)))
                      else
                        (do
                          let w__132 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (ICC_CTLR_NS_write (Mk_ICC_CTLR_Type w__132)))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ICV_EOIR0_SysRegWrite32_a5e151ee536f5632 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FIQ : (BitVec 1) := (_get_SCR_EL3_Type_FIQ w__1)
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_M : (BitVec 5) := w__2.M
  let w__3 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_FIQ : (BitVec 1) := (_get_SCR_Type_FIQ w__3)
  let w__4 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T12 : (BitVec 1) := (_get_HSTR_EL2_Type_T12 w__4)
  let w__5 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T12 : (BitVec 1) := (_get_HSTR_Type_T12 w__5)
  let w__6 ← (( do (ICC_SRE_read ()) ) : SailM (BitVec 32) )
  let __ICC_SRE_SRE : (BitVec 1) := (_get_ICC_SRE_Type_SRE w__6)
  let w__7 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  let __ICH_HCR_EL2_TALL0 : (BitVec 1) := (_get_ICH_HCR_EL2_Type_TALL0 w__7)
  let w__8 ← (( do (ICH_HCR_read ()) ) : SailM (BitVec 32) )
  let __ICH_HCR_TALL0 : (BitVec 1) := (_get_ICH_HCR_Type_TALL0 w__8)
  let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_FMO : (BitVec 1) := (_get_HCR_EL2_Type_FMO w__9)
  let w__10 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_FMO : (BitVec 1) := (_get_HCR_Type_FMO w__10)
  let w__11 ← (( do (ICC_HSRE_read ()) ) : SailM (BitVec 32) )
  let __ICC_HSRE_SRE : (BitVec 1) := (_get_ICC_HSRE_Type_SRE w__11)
  let w__12 ← (( do readReg ICC_MSRE ) : SailM (BitVec 32) )
  let __ICC_MSRE_SRE : (BitVec 1) := (_get_ICC_MSRE_Type_SRE w__12)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__21 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                            then
                              (do
                                let w__15 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__15) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__19 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__19) : Bool))))
                  else (pure false)) && ((__SCR_EL3_FIQ == 1#1) : Bool))) ) : SailM Bool )
          if (w__21 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__31 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 if ((← do
                                      if ((← do
                                           (pure ((← do
                                                 (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                      then
                                        (do
                                          let w__24 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32)
                                            )
                                          (pure ((((_get_EDSCR_Type_SDD w__24) == 1#1) : Bool))))
                                      else (pure false)) : Bool)
                                 then
                                   (do
                                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                                 else (pure false)) : Bool)
                            then
                              (do
                                (ELUsingAArch32 EL3))
                            else (pure false)) && ((__PSTATE_M != M32_Monitor) : Bool)))) && ((__SCR_FIQ == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__31 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__35 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__33 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__33) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T12 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__35 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__39 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HSTR_T12 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__39 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          if ((__ICC_SRE_SRE == 0#1) : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              let w__43 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          let w__41 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                          (pure (((! w__41) : Bool))))
                                      else (pure false)) && ((__ICH_HCR_EL2_TALL0 == 1#1) : Bool)))
                                ) : SailM Bool )
                              if (w__43 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__47 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (EL2Enabled ())) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL2))
                                          else (pure false)) && ((__ICH_HCR_TALL0 == 1#1) : Bool)))
                                    ) : SailM Bool )
                                  if (w__47 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      let w__51 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (EL2Enabled ())) : Bool)
                                              then
                                                (do
                                                  let w__49 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                    Bool )
                                                  (pure (((! w__49) : Bool))))
                                              else (pure false)) && ((__HCR_EL2_FMO == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__51 : Bool)
                                      then
                                        (do
                                          let w__52 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                          (ICV_EOIR0_write (Mk_ICV_EOIR0_Type w__52)))
                                      else
                                        (do
                                          let w__56 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       (EL2Enabled ())) : Bool)
                                                  then
                                                    (do
                                                      (ELUsingAArch32 EL2))
                                                  else (pure false)) && ((__HCR_FMO == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__56 : Bool)
                                          then
                                            (do
                                              let w__57 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                              (ICV_EOIR0_write (Mk_ICV_EOIR0_Type w__57)))
                                          else
                                            (do
                                              let w__60 ← (( do
                                                (pure ((← do
                                                      if (((HaveEL EL3) : Bool) : Bool)
                                                      then
                                                        (do
                                                          let w__58 ← (( do (ELUsingAArch32 EL3) )
                                                            : SailM Bool )
                                                          (pure (((! w__58) : Bool))))
                                                      else (pure false)) && ((__SCR_EL3_FIQ == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__60 : Bool)
                                              then
                                                (do
                                                  let w__63 ← (( do
                                                    if ((← do
                                                         (Halted ())) : Bool)
                                                    then
                                                      (do
                                                        let w__62 ← (( do (EDSCR_read ()) ) :
                                                          SailM (BitVec 32) )
                                                        (pure ((((_get_EDSCR_Type_SDD w__62) == 1#1) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__63 : Bool)
                                                  then sailThrow ((Error_Undefined ()))
                                                  else
                                                    (do
                                                      (AArch64_AArch32SystemAccessTrap EL3
                                                        (BitVec.toNat 0x03#8))))
                                              else
                                                (do
                                                  let w__67 ← (( do
                                                    (pure ((← do
                                                          (pure ((← do
                                                                if (((HaveEL EL3) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    (ELUsingAArch32 EL3))
                                                                else (pure false)) && ((__PSTATE_M != M32_Monitor) : Bool)))) && ((__SCR_FIQ == 1#1) : Bool)))
                                                    ) : SailM Bool )
                                                  if (w__67 : Bool)
                                                  then
                                                    (do
                                                      let w__70 ← (( do
                                                        if ((← do
                                                             (Halted ())) : Bool)
                                                        then
                                                          (do
                                                            let w__69 ← (( do (EDSCR_read ()) ) :
                                                              SailM (BitVec 32) )
                                                            (pure ((((_get_EDSCR_Type_SDD w__69) == 1#1) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__70 : Bool)
                                                      then sailThrow ((Error_Undefined ()))
                                                      else
                                                        (do
                                                          (AArch32_TakeMonitorTrapException ())))
                                                  else
                                                    (do
                                                      let w__71 ← (( do (R_read t) ) : SailM
                                                        (BitVec 32) )
                                                      (ICC_EOIR0_write (Mk_ICC_EOIR0_Type w__71))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__80 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                then
                                  (do
                                    let w__74 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__74) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__78 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__78) : Bool))))
                      else (pure false)) && ((__SCR_EL3_FIQ == 1#1) : Bool))) ) : SailM Bool )
              if (w__80 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__89 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         (pure ((← do
                                               (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                    then
                                      (do
                                        let w__83 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__83) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL3))
                          else (pure false)) && ((__SCR_FIQ == 1#1) : Bool))) ) : SailM Bool )
                  if (w__89 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__ICC_HSRE_SRE == 0#1) : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__92 ← (( do
                            (pure ((← do
                                  if (((HaveEL EL3) : Bool) : Bool)
                                  then
                                    (do
                                      let w__90 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__90) : Bool))))
                                  else (pure false)) && ((__SCR_EL3_FIQ == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__92 : Bool)
                          then
                            (do
                              let w__95 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__94 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__94) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__95 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                          else
                            (do
                              let w__98 ← (( do
                                (pure ((← do
                                      if (((HaveEL EL3) : Bool) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL3))
                                      else (pure false)) && ((__SCR_FIQ == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__98 : Bool)
                              then
                                (do
                                  let w__101 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__100 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__100) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__101 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch32_TakeMonitorTrapException ())))
                              else
                                (do
                                  let w__102 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (ICC_EOIR0_write (Mk_ICC_EOIR0_Type w__102))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__103 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (ICC_EOIR0_write (Mk_ICC_EOIR0_Type w__103))))
              else (pure (())))))


end ArmFull.Functions
