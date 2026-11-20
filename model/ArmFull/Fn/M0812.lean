module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0054
public import ArmFull.Fn.M0055
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0070
public import ArmFull.Fn.M0075
public import ArmFull.Fn.M0081
public import ArmFull.Fn.M0082
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0199
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0252
public import ArmFull.Fn.M0253
public import ArmFull.Fn.M0258 set_option backward.proofsInPublic true @[expose] public section

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
def ICV_AP0R_SysRegWrite32_b2c1de53009da653 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__22 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 if ((← do
                                      (Halted ())) : Bool)
                                 then
                                   (do
                                     (HaveEL EL3))
                                 else (pure false)) : Bool)
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
                  else (pure false)) && ((__SCR_EL3_FIQ == 1#1) : Bool))) ) : SailM Bool )
          if (w__22 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__33 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 if ((← do
                                      if ((← do
                                           if ((← do
                                                (Halted ())) : Bool)
                                           then
                                             (do
                                               (HaveEL EL3))
                                           else (pure false)) : Bool)
                                      then
                                        (do
                                          let w__26 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32)
                                            )
                                          (pure ((((_get_EDSCR_Type_SDD w__26) == 1#1) : Bool))))
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
              if (w__33 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__37 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__35 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__35) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T12 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__37 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__41 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HSTR_T12 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__41 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          if ((__ICC_SRE_SRE == 0#1) : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              let w__45 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          let w__43 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                          (pure (((! w__43) : Bool))))
                                      else (pure false)) && ((__ICH_HCR_EL2_TALL0 == 1#1) : Bool)))
                                ) : SailM Bool )
                              if (w__45 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__49 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (EL2Enabled ())) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL2))
                                          else (pure false)) && ((__ICH_HCR_TALL0 == 1#1) : Bool)))
                                    ) : SailM Bool )
                                  if (w__49 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      let w__53 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (EL2Enabled ())) : Bool)
                                              then
                                                (do
                                                  let w__51 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                    Bool )
                                                  (pure (((! w__51) : Bool))))
                                              else (pure false)) && ((__HCR_EL2_FMO == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__53 : Bool)
                                      then
                                        (do
                                          let w__54 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                          (ICV_AP0R_set 0 w__54))
                                      else
                                        (do
                                          let w__58 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       (EL2Enabled ())) : Bool)
                                                  then
                                                    (do
                                                      (ELUsingAArch32 EL2))
                                                  else (pure false)) && ((__HCR_FMO == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__58 : Bool)
                                          then
                                            (do
                                              let w__59 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                              (ICV_AP0R_set 0 w__59))
                                          else
                                            (do
                                              let w__63 ← (( do
                                                (pure ((← do
                                                      if ((← do
                                                           (HaveEL EL3)) : Bool)
                                                      then
                                                        (do
                                                          let w__61 ← (( do (ELUsingAArch32 EL3) )
                                                            : SailM Bool )
                                                          (pure (((! w__61) : Bool))))
                                                      else (pure false)) && ((__SCR_EL3_FIQ == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__63 : Bool)
                                              then
                                                (do
                                                  let w__66 ← (( do
                                                    if ((← do
                                                         (Halted ())) : Bool)
                                                    then
                                                      (do
                                                        let w__65 ← (( do (EDSCR_read ()) ) :
                                                          SailM (BitVec 32) )
                                                        (pure ((((_get_EDSCR_Type_SDD w__65) == 1#1) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__66 : Bool)
                                                  then sailThrow ((Error_Undefined ()))
                                                  else
                                                    (do
                                                      (AArch64_AArch32SystemAccessTrap EL3
                                                        (BitVec.toNat 0x03#8))))
                                              else
                                                (do
                                                  let w__71 ← (( do
                                                    (pure ((← do
                                                          (pure ((← do
                                                                if ((← do
                                                                     (HaveEL EL3)) : Bool)
                                                                then
                                                                  (do
                                                                    (ELUsingAArch32 EL3))
                                                                else (pure false)) && ((__PSTATE_M != M32_Monitor) : Bool)))) && ((__SCR_FIQ == 1#1) : Bool)))
                                                    ) : SailM Bool )
                                                  if (w__71 : Bool)
                                                  then
                                                    (do
                                                      let w__74 ← (( do
                                                        if ((← do
                                                             (Halted ())) : Bool)
                                                        then
                                                          (do
                                                            let w__73 ← (( do (EDSCR_read ()) ) :
                                                              SailM (BitVec 32) )
                                                            (pure ((((_get_EDSCR_Type_SDD w__73) == 1#1) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__74 : Bool)
                                                      then sailThrow ((Error_Undefined ()))
                                                      else
                                                        (do
                                                          (AArch32_TakeMonitorTrapException ())))
                                                  else
                                                    (do
                                                      let w__75 ← (( do (R_read t) ) : SailM
                                                        (BitVec 32) )
                                                      (ICC_AP0R_set 0 w__75)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__85 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     if ((← do
                                          (Halted ())) : Bool)
                                     then
                                       (do
                                         (HaveEL EL3))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__79 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__79) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__83 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__83) : Bool))))
                      else (pure false)) && ((__SCR_EL3_FIQ == 1#1) : Bool))) ) : SailM Bool )
              if (w__85 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__95 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         if ((← do
                                              (Halted ())) : Bool)
                                         then
                                           (do
                                             (HaveEL EL3))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__89 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__89) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL3))
                          else (pure false)) && ((__SCR_FIQ == 1#1) : Bool))) ) : SailM Bool )
                  if (w__95 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__ICC_HSRE_SRE == 0#1) : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__99 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (HaveEL EL3)) : Bool)
                                  then
                                    (do
                                      let w__97 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__97) : Bool))))
                                  else (pure false)) && ((__SCR_EL3_FIQ == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__99 : Bool)
                          then
                            (do
                              let w__102 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__101 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__101) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__102 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                          else
                            (do
                              let w__106 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL3))
                                      else (pure false)) && ((__SCR_FIQ == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__106 : Bool)
                              then
                                (do
                                  let w__109 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__108 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__108) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__109 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch32_TakeMonitorTrapException ())))
                              else
                                (do
                                  let w__110 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (ICC_AP0R_set 0 w__110)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__111 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (ICC_AP0R_set 0 w__111)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ICV_AP1R_SysRegWrite32_fcd6d6e80a079de9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__23 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 if ((← do
                                      (Halted ())) : Bool)
                                 then
                                   (do
                                     (HaveEL EL3))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__17 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__17) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__21 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__21) : Bool))))
                  else (pure false)) && ((__SCR_EL3_IRQ == 1#1) : Bool))) ) : SailM Bool )
          if (w__23 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__34 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 if ((← do
                                      if ((← do
                                           if ((← do
                                                (Halted ())) : Bool)
                                           then
                                             (do
                                               (HaveEL EL3))
                                           else (pure false)) : Bool)
                                      then
                                        (do
                                          let w__27 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32)
                                            )
                                          (pure ((((_get_EDSCR_Type_SDD w__27) == 1#1) : Bool))))
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
                          if ((__ICC_SRE_SRE == 0#1) : Bool)
                          then sailThrow ((Error_Undefined ()))
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
                                      else (pure false)) && ((__ICH_HCR_EL2_TALL1 == 1#1) : Bool)))
                                ) : SailM Bool )
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
                                          else (pure false)) && ((__ICH_HCR_TALL1 == 1#1) : Bool)))
                                    ) : SailM Bool )
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
                                              else (pure false)) && ((__HCR_EL2_IMO == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__54 : Bool)
                                      then
                                        (do
                                          let w__55 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                          (ICV_AP1R_set 0 w__55))
                                      else
                                        (do
                                          let w__59 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       (EL2Enabled ())) : Bool)
                                                  then
                                                    (do
                                                      (ELUsingAArch32 EL2))
                                                  else (pure false)) && ((__HCR_IMO == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__59 : Bool)
                                          then
                                            (do
                                              let w__60 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                              (ICV_AP1R_set 0 w__60))
                                          else
                                            (do
                                              let w__64 ← (( do
                                                (pure ((← do
                                                      if ((← do
                                                           (HaveEL EL3)) : Bool)
                                                      then
                                                        (do
                                                          let w__62 ← (( do (ELUsingAArch32 EL3) )
                                                            : SailM Bool )
                                                          (pure (((! w__62) : Bool))))
                                                      else (pure false)) && ((__SCR_EL3_IRQ == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__64 : Bool)
                                              then
                                                (do
                                                  let w__67 ← (( do
                                                    if ((← do
                                                         (Halted ())) : Bool)
                                                    then
                                                      (do
                                                        let w__66 ← (( do (EDSCR_read ()) ) :
                                                          SailM (BitVec 32) )
                                                        (pure ((((_get_EDSCR_Type_SDD w__66) == 1#1) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__67 : Bool)
                                                  then sailThrow ((Error_Undefined ()))
                                                  else
                                                    (do
                                                      (AArch64_AArch32SystemAccessTrap EL3
                                                        (BitVec.toNat 0x03#8))))
                                              else
                                                (do
                                                  let w__72 ← (( do
                                                    (pure ((← do
                                                          (pure ((← do
                                                                if ((← do
                                                                     (HaveEL EL3)) : Bool)
                                                                then
                                                                  (do
                                                                    (ELUsingAArch32 EL3))
                                                                else (pure false)) && ((__PSTATE_M != M32_Monitor) : Bool)))) && ((__SCR_IRQ == 1#1) : Bool)))
                                                    ) : SailM Bool )
                                                  if (w__72 : Bool)
                                                  then
                                                    (do
                                                      let w__75 ← (( do
                                                        if ((← do
                                                             (Halted ())) : Bool)
                                                        then
                                                          (do
                                                            let w__74 ← (( do (EDSCR_read ()) ) :
                                                              SailM (BitVec 32) )
                                                            (pure ((((_get_EDSCR_Type_SDD w__74) == 1#1) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__75 : Bool)
                                                      then sailThrow ((Error_Undefined ()))
                                                      else
                                                        (do
                                                          (AArch32_TakeMonitorTrapException ())))
                                                  else
                                                    (do
                                                      let w__76 ← (( do (HaveEL EL3) ) : SailM
                                                        Bool )
                                                      if (w__76 : Bool)
                                                      then
                                                        (do
                                                          let w__77 ← (( do (R_read t) ) : SailM
                                                            (BitVec 32) )
                                                          (ICC_AP1R_NS_set 0 w__77))
                                                      else
                                                        (do
                                                          let w__78 ← (( do (R_read t) ) : SailM
                                                            (BitVec 32) )
                                                          (ICC_AP1R_set 0 w__78))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__88 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     if ((← do
                                          (Halted ())) : Bool)
                                     then
                                       (do
                                         (HaveEL EL3))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__82 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__82) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__86 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__86) : Bool))))
                      else (pure false)) && ((__SCR_EL3_IRQ == 1#1) : Bool))) ) : SailM Bool )
              if (w__88 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__98 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         if ((← do
                                              (Halted ())) : Bool)
                                         then
                                           (do
                                             (HaveEL EL3))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__92 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__92) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL3))
                          else (pure false)) && ((__SCR_IRQ == 1#1) : Bool))) ) : SailM Bool )
                  if (w__98 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__ICC_HSRE_SRE == 0#1) : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__102 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (HaveEL EL3)) : Bool)
                                  then
                                    (do
                                      let w__100 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__100) : Bool))))
                                  else (pure false)) && ((__SCR_EL3_IRQ == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__102 : Bool)
                          then
                            (do
                              let w__105 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__104 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__104) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__105 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                          else
                            (do
                              let w__109 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL3))
                                      else (pure false)) && ((__SCR_IRQ == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__109 : Bool)
                              then
                                (do
                                  let w__112 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__111 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__111) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__112 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch32_TakeMonitorTrapException ())))
                              else
                                (do
                                  let w__113 ← (( do (HaveEL EL3) ) : SailM Bool )
                                  if (w__113 : Bool)
                                  then
                                    (do
                                      let w__114 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      (ICC_AP1R_NS_set 0 w__114))
                                  else
                                    (do
                                      let w__115 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      (ICC_AP1R_set 0 w__115))))))))
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
                          let w__116 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (ICC_AP1R_S_set 0 w__116))
                      else
                        (do
                          let w__117 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (ICC_AP1R_NS_set 0 w__117))))
              else (pure (())))))


end ArmFull.Functions
