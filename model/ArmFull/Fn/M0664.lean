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
import ArmFull.Fn.M0059
import ArmFull.Fn.M0070
import ArmFull.Fn.M0075
import ArmFull.Fn.M0100
import ArmFull.Fn.M0140
import ArmFull.Fn.M0141
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0199
import ArmFull.Fn.M0203
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
def ICV_IGRPEN1_SysRegRead32_9335bbfc906f43aa (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_IRQ : (BitVec 1) := (_get_SCR_EL3_Type_IRQ w__1)
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_M : (BitVec 5) := w__2.M
  let w__3 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_IRQ : (BitVec 1) := (_get_SCR_Type_IRQ w__3)
  let w__4 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T12 : (BitVec 1) := (_get_HSTR_EL2_Type_T12 w__4)
  let w__5 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T12 : (BitVec 1) := (_get_HSTR_Type_T12 w__5)
  let w__6 ← (( do (ICC_SRE_read ()) ) : SailM (BitVec 32) )
  let __ICC_SRE_SRE : (BitVec 1) := (_get_ICC_SRE_Type_SRE w__6)
  let w__7 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  let __ICH_HCR_EL2_TALL1 : (BitVec 1) := (_get_ICH_HCR_EL2_Type_TALL1 w__7)
  let w__8 ← (( do (ICH_HCR_read ()) ) : SailM (BitVec 32) )
  let __ICH_HCR_TALL1 : (BitVec 1) := (_get_ICH_HCR_Type_TALL1 w__8)
  let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_IMO : (BitVec 1) := (_get_HCR_EL2_Type_IMO w__9)
  let w__10 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_IMO : (BitVec 1) := (_get_HCR_Type_IMO w__10)
  let w__11 ← (( do (ICC_HSRE_read ()) ) : SailM (BitVec 32) )
  let __ICC_HSRE_SRE : (BitVec 1) := (_get_ICC_HSRE_Type_SRE w__11)
  let w__12 ← (( do readReg ICC_MSRE ) : SailM (BitVec 32) )
  let __ICC_MSRE_SRE : (BitVec 1) := (_get_ICC_MSRE_Type_SRE w__12)
  let w__13 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__13)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__22 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                            then
                              (do
                                let w__16 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__16) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__20 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__20) : Bool))))
                  else (pure false)) && ((__SCR_EL3_IRQ == 1#1) : Bool))) ) : SailM Bool )
          if (w__22 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__32 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 if ((← do
                                      if ((← do
                                           (pure ((← do
                                                 (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                      then
                                        (do
                                          let w__25 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32)
                                            )
                                          (pure ((((_get_EDSCR_Type_SDD w__25) == 1#1) : Bool))))
                                      else (pure false)) : Bool)
                                 then
                                   (do
                                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                                 else (pure false)) : Bool)
                            then
                              (do
                                (ELUsingAArch32 EL3))
                            else (pure false)) && ((__PSTATE_M != M32_Monitor) : Bool)))) && ((__SCR_IRQ == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__32 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__36 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__34 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__34) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T12 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__36 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__40 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HSTR_T12 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__40 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          if ((__ICC_SRE_SRE == 0#1) : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              let w__44 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          let w__42 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                          (pure (((! w__42) : Bool))))
                                      else (pure false)) && ((__ICH_HCR_EL2_TALL1 == 1#1) : Bool)))
                                ) : SailM Bool )
                              if (w__44 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__48 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (EL2Enabled ())) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL2))
                                          else (pure false)) && ((__ICH_HCR_TALL1 == 1#1) : Bool)))
                                    ) : SailM Bool )
                                  if (w__48 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      let w__52 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (EL2Enabled ())) : Bool)
                                              then
                                                (do
                                                  let w__50 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                    Bool )
                                                  (pure (((! w__50) : Bool))))
                                              else (pure false)) && ((__HCR_EL2_IMO == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__52 : Bool)
                                      then
                                        (do
                                          let w__53 ← (( do (ICV_IGRPEN1_read ()) ) : SailM
                                            (BitVec 32) )
                                          (R_set t (__get_ICV_IGRPEN1 w__53)))
                                      else
                                        (do
                                          let w__57 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       (EL2Enabled ())) : Bool)
                                                  then
                                                    (do
                                                      (ELUsingAArch32 EL2))
                                                  else (pure false)) && ((__HCR_IMO == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__57 : Bool)
                                          then
                                            (do
                                              let w__58 ← (( do (ICV_IGRPEN1_read ()) ) : SailM
                                                (BitVec 32) )
                                              (R_set t (__get_ICV_IGRPEN1 w__58)))
                                          else
                                            (do
                                              let w__61 ← (( do
                                                (pure ((← do
                                                      if (((HaveEL EL3) : Bool) : Bool)
                                                      then
                                                        (do
                                                          let w__59 ← (( do (ELUsingAArch32 EL3) )
                                                            : SailM Bool )
                                                          (pure (((! w__59) : Bool))))
                                                      else (pure false)) && ((__SCR_EL3_IRQ == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__61 : Bool)
                                              then
                                                (do
                                                  let w__64 ← (( do
                                                    if ((← do
                                                         (Halted ())) : Bool)
                                                    then
                                                      (do
                                                        let w__63 ← (( do (EDSCR_read ()) ) :
                                                          SailM (BitVec 32) )
                                                        (pure ((((_get_EDSCR_Type_SDD w__63) == 1#1) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__64 : Bool)
                                                  then sailThrow ((Error_Undefined ()))
                                                  else
                                                    (do
                                                      (AArch64_AArch32SystemAccessTrap EL3
                                                        (BitVec.toNat 0x03#8))))
                                              else
                                                (do
                                                  let w__68 ← (( do
                                                    (pure ((← do
                                                          (pure ((← do
                                                                if (((HaveEL EL3) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    (ELUsingAArch32 EL3))
                                                                else (pure false)) && ((__PSTATE_M != M32_Monitor) : Bool)))) && ((__SCR_IRQ == 1#1) : Bool)))
                                                    ) : SailM Bool )
                                                  if (w__68 : Bool)
                                                  then
                                                    (do
                                                      let w__71 ← (( do
                                                        if ((← do
                                                             (Halted ())) : Bool)
                                                        then
                                                          (do
                                                            let w__70 ← (( do (EDSCR_read ()) ) :
                                                              SailM (BitVec 32) )
                                                            (pure ((((_get_EDSCR_Type_SDD w__70) == 1#1) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__71 : Bool)
                                                      then sailThrow ((Error_Undefined ()))
                                                      else
                                                        (do
                                                          (AArch32_TakeMonitorTrapException ())))
                                                  else
                                                    (do
                                                      if ((HaveEL EL3) : Bool)
                                                      then
                                                        (do
                                                          let w__72 ← (( do
                                                            (ICC_IGRPEN1_NS_read ()) ) : SailM
                                                            (BitVec 32) )
                                                          (R_set t (__get_ICC_IGRPEN1_NS w__72)))
                                                      else
                                                        (do
                                                          let w__73 ← (( do (ICC_IGRPEN1_read ())
                                                            ) : SailM (BitVec 32) )
                                                          (R_set t (__get_ICC_IGRPEN1 w__73)))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__82 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                then
                                  (do
                                    let w__76 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__76) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__80 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__80) : Bool))))
                      else (pure false)) && ((__SCR_EL3_IRQ == 1#1) : Bool))) ) : SailM Bool )
              if (w__82 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__91 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         (pure ((← do
                                               (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                    then
                                      (do
                                        let w__85 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__85) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL3))
                          else (pure false)) && ((__SCR_IRQ == 1#1) : Bool))) ) : SailM Bool )
                  if (w__91 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__ICC_HSRE_SRE == 0#1) : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__94 ← (( do
                            (pure ((← do
                                  if (((HaveEL EL3) : Bool) : Bool)
                                  then
                                    (do
                                      let w__92 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__92) : Bool))))
                                  else (pure false)) && ((__SCR_EL3_IRQ == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__94 : Bool)
                          then
                            (do
                              let w__97 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__96 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__96) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__97 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                          else
                            (do
                              let w__100 ← (( do
                                (pure ((← do
                                      if (((HaveEL EL3) : Bool) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL3))
                                      else (pure false)) && ((__SCR_IRQ == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__100 : Bool)
                              then
                                (do
                                  let w__103 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__102 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__102) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__103 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch32_TakeMonitorTrapException ())))
                              else
                                (do
                                  if ((HaveEL EL3) : Bool)
                                  then
                                    (do
                                      let w__104 ← (( do (ICC_IGRPEN1_NS_read ()) ) : SailM
                                        (BitVec 32) )
                                      (R_set t (__get_ICC_IGRPEN1_NS w__104)))
                                  else
                                    (do
                                      let w__105 ← (( do (ICC_IGRPEN1_read ()) ) : SailM
                                        (BitVec 32) )
                                      (R_set t (__get_ICC_IGRPEN1 w__105)))))))))
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
                          let w__106 ← (( do (ICC_IGRPEN1_S_read ()) ) : SailM (BitVec 32) )
                          (R_set t (__get_ICC_IGRPEN1_S w__106)))
                      else
                        (do
                          let w__107 ← (( do (ICC_IGRPEN1_NS_read ()) ) : SailM (BitVec 32) )
                          (R_set t (__get_ICC_IGRPEN1_NS w__107)))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ICV_RPR_SysRegRead32_ce7e7d8c013c544d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__22 ← (( do
            if ((← do
                 if ((← do
                      if ((← do
                           if ((← do
                                (pure ((← do
                                      (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                           then
                             (do
                               let w__14 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                               (pure ((((_get_EDSCR_Type_SDD w__14) == 1#1) : Bool))))
                           else (pure false)) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) : Bool)
                 then
                   (do
                     let w__18 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                     (pure (((! w__18) : Bool))))
                 else (pure false)) : Bool)
            then
              (do
                let w__20 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                let w__21 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                (pure (((((_get_SCR_EL3_Type_IRQ w__20) +++ (_get_SCR_EL3_Type_FIQ w__21)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__22 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__34 ← (( do
                if ((← do
                     (pure ((← do
                           if ((← do
                                if ((← do
                                     if ((← do
                                          (pure ((← do
                                                (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                     then
                                       (do
                                         let w__25 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                         (pure ((((_get_EDSCR_Type_SDD w__25) == 1#1) : Bool))))
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
                    let w__32 ← (( do readReg SCR ) : SailM (BitVec 32) )
                    let w__33 ← (( do readReg SCR ) : SailM (BitVec 32) )
                    (pure (((((_get_SCR_Type_IRQ w__32) +++ (_get_SCR_Type_FIQ w__33)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__34 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__38 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__36 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__36) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T12 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__38 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__42 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HSTR_T12 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__42 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__46 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__44 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                      (pure (((! w__44) : Bool))))
                                  else (pure false)) && ((__ICH_HCR_EL2_TC == 1#1) : Bool))) ) :
                            SailM Bool )
                          if (w__46 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__50 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__ICH_HCR_TC == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__50 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__54 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (EL2Enabled ())) : Bool)
                                          then
                                            (do
                                              let w__52 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                Bool )
                                              (pure (((! w__52) : Bool))))
                                          else (pure false)) && ((__HCR_EL2_FMO == 1#1) : Bool))) )
                                    : SailM Bool )
                                  if (w__54 : Bool)
                                  then
                                    (do
                                      let w__55 ← (( do (ICV_RPR_read ()) ) : SailM (BitVec 32) )
                                      (R_set t (__get_ICV_RPR w__55)))
                                  else
                                    (do
                                      let w__59 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (EL2Enabled ())) : Bool)
                                              then
                                                (do
                                                  let w__57 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                    Bool )
                                                  (pure (((! w__57) : Bool))))
                                              else (pure false)) && ((__HCR_EL2_IMO == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__59 : Bool)
                                      then
                                        (do
                                          let w__60 ← (( do (ICV_RPR_read ()) ) : SailM
                                            (BitVec 32) )
                                          (R_set t (__get_ICV_RPR w__60)))
                                      else
                                        (do
                                          let w__64 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       (EL2Enabled ())) : Bool)
                                                  then
                                                    (do
                                                      (ELUsingAArch32 EL2))
                                                  else (pure false)) && ((__HCR_FMO == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__64 : Bool)
                                          then
                                            (do
                                              let w__65 ← (( do (ICV_RPR_read ()) ) : SailM
                                                (BitVec 32) )
                                              (R_set t (__get_ICV_RPR w__65)))
                                          else
                                            (do
                                              let w__69 ← (( do
                                                (pure ((← do
                                                      if ((← do
                                                           (EL2Enabled ())) : Bool)
                                                      then
                                                        (do
                                                          (ELUsingAArch32 EL2))
                                                      else (pure false)) && ((__HCR_IMO == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__69 : Bool)
                                              then
                                                (do
                                                  let w__70 ← (( do (ICV_RPR_read ()) ) : SailM
                                                    (BitVec 32) )
                                                  (R_set t (__get_ICV_RPR w__70)))
                                              else
                                                (do
                                                  let w__75 ← (( do
                                                    if ((← do
                                                         if (((HaveEL EL3) : Bool) : Bool)
                                                         then
                                                           (do
                                                             let w__71 ← (( do
                                                               (ELUsingAArch32 EL3) ) : SailM Bool )
                                                             (pure (((! w__71) : Bool))))
                                                         else (pure false)) : Bool)
                                                    then
                                                      (do
                                                        let w__73 ← (( do readReg SCR_EL3 ) :
                                                          SailM (BitVec 64) )
                                                        let w__74 ← (( do readReg SCR_EL3 ) :
                                                          SailM (BitVec 64) )
                                                        (pure (((((_get_SCR_EL3_Type_IRQ w__73) +++ (_get_SCR_EL3_Type_FIQ
                                                                w__74)) == 0b11#2) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__75 : Bool)
                                                  then
                                                    (do
                                                      let w__78 ← (( do
                                                        if ((← do
                                                             (Halted ())) : Bool)
                                                        then
                                                          (do
                                                            let w__77 ← (( do (EDSCR_read ()) ) :
                                                              SailM (BitVec 32) )
                                                            (pure ((((_get_EDSCR_Type_SDD w__77) == 1#1) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__78 : Bool)
                                                      then sailThrow ((Error_Undefined ()))
                                                      else
                                                        (do
                                                          (AArch64_AArch32SystemAccessTrap EL3
                                                            (BitVec.toNat 0x03#8))))
                                                  else
                                                    (do
                                                      let w__84 ← (( do
                                                        if ((← do
                                                             (pure ((← do
                                                                   if (((HaveEL EL3) : Bool) : Bool)
                                                                   then
                                                                     (do
                                                                       (ELUsingAArch32 EL3))
                                                                   else (pure false)) && ((__PSTATE_M != M32_Monitor) : Bool)))) : Bool)
                                                        then
                                                          (do
                                                            let w__82 ← (( do readReg SCR ) :
                                                              SailM (BitVec 32) )
                                                            let w__83 ← (( do readReg SCR ) :
                                                              SailM (BitVec 32) )
                                                            (pure (((((_get_SCR_Type_IRQ w__82) +++ (_get_SCR_Type_FIQ
                                                                    w__83)) == 0b11#2) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__84 : Bool)
                                                      then
                                                        (do
                                                          let w__87 ← (( do
                                                            if ((← do
                                                                 (Halted ())) : Bool)
                                                            then
                                                              (do
                                                                let w__86 ← (( do (EDSCR_read ())
                                                                  ) : SailM (BitVec 32) )
                                                                (pure ((((_get_EDSCR_Type_SDD w__86) == 1#1) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__87 : Bool)
                                                          then sailThrow ((Error_Undefined ()))
                                                          else
                                                            (do
                                                              (AArch32_TakeMonitorTrapException ())))
                                                      else
                                                        (do
                                                          let w__88 ← (( do (ICC_RPR_read ()) ) :
                                                            SailM (BitVec 32) )
                                                          (R_set t (__get_ICC_RPR w__88)))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__99 ← (( do
                if ((← do
                     if ((← do
                          if ((← do
                               if ((← do
                                    (pure ((← do
                                          (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                               then
                                 (do
                                   let w__91 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                   (pure ((((_get_EDSCR_Type_SDD w__91) == 1#1) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) : Bool)
                     then
                       (do
                         let w__95 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                         (pure (((! w__95) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__97 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    let w__98 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    (pure (((((_get_SCR_EL3_Type_IRQ w__97) +++ (_get_SCR_EL3_Type_FIQ w__98)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__99 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__110 ← (( do
                    if ((← do
                         if ((← do
                              if ((← do
                                   if ((← do
                                        (pure ((← do
                                              (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                   then
                                     (do
                                       let w__102 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                       (pure ((((_get_EDSCR_Type_SDD w__102) == 1#1) : Bool))))
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
                        let w__108 ← (( do readReg SCR ) : SailM (BitVec 32) )
                        let w__109 ← (( do readReg SCR ) : SailM (BitVec 32) )
                        (pure (((((_get_SCR_Type_IRQ w__108) +++ (_get_SCR_Type_FIQ w__109)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__110 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__ICC_HSRE_SRE == 0#1) : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__115 ← (( do
                            if ((← do
                                 if (((HaveEL EL3) : Bool) : Bool)
                                 then
                                   (do
                                     let w__111 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                     (pure (((! w__111) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__113 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                let w__114 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                (pure (((((_get_SCR_EL3_Type_IRQ w__113) +++ (_get_SCR_EL3_Type_FIQ
                                        w__114)) == 0b11#2) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__115 : Bool)
                          then
                            (do
                              let w__118 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__117 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__117) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__118 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                          else
                            (do
                              let w__123 ← (( do
                                if ((← do
                                     if (((HaveEL EL3) : Bool) : Bool)
                                     then
                                       (do
                                         (ELUsingAArch32 EL3))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__121 ← (( do readReg SCR ) : SailM (BitVec 32) )
                                    let w__122 ← (( do readReg SCR ) : SailM (BitVec 32) )
                                    (pure (((((_get_SCR_Type_IRQ w__121) +++ (_get_SCR_Type_FIQ
                                            w__122)) == 0b11#2) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__123 : Bool)
                              then
                                (do
                                  let w__126 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__125 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__125) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__126 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch32_TakeMonitorTrapException ())))
                              else
                                (do
                                  let w__127 ← (( do (ICC_RPR_read ()) ) : SailM (BitVec 32) )
                                  (R_set t (__get_ICC_RPR w__127))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__128 ← (( do (ICC_RPR_read ()) ) : SailM (BitVec 32) )
                      (R_set t (__get_ICC_RPR w__128))))
              else (pure (())))))


end ArmFull.Functions
