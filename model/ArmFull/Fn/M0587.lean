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
import ArmFull.Fn.M0047
import ArmFull.Fn.M0054
import ArmFull.Fn.M0056
import ArmFull.Fn.M0059
import ArmFull.Fn.M0063
import ArmFull.Fn.M0064
import ArmFull.Fn.M0070
import ArmFull.Fn.M0073
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0199
import ArmFull.Fn.M0200
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

/-- Type quantifiers: t : Int, t2 : Int -/
def ICC_SGI1R_SysRegWrite64_e5d73969c7266f22 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_M : (BitVec 5) := w__1.M
  let w__2 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T12 : (BitVec 1) := (_get_HSTR_EL2_Type_T12 w__2)
  let w__3 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T12 : (BitVec 1) := (_get_HSTR_Type_T12 w__3)
  let w__4 ← (( do (ICC_SRE_read ()) ) : SailM (BitVec 32) )
  let __ICC_SRE_SRE : (BitVec 1) := (_get_ICC_SRE_Type_SRE w__4)
  let w__5 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  let __ICH_HCR_EL2_TC : (BitVec 1) := (_get_ICH_HCR_EL2_Type_TC w__5)
  let w__6 ← (( do (ICH_HCR_read ()) ) : SailM (BitVec 32) )
  let __ICH_HCR_TC : (BitVec 1) := (_get_ICH_HCR_Type_TC w__6)
  let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_FMO : (BitVec 1) := (_get_HCR_EL2_Type_FMO w__7)
  let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_IMO : (BitVec 1) := (_get_HCR_EL2_Type_IMO w__8)
  let w__9 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_FMO : (BitVec 1) := (_get_HCR_Type_FMO w__9)
  let w__10 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_IMO : (BitVec 1) := (_get_HCR_Type_IMO w__10)
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
                          if ((__ICC_SRE_SRE == 0#1) : Bool)
                          then sailThrow ((Error_Undefined ()))
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
                                              else (pure false)) && ((__HCR_EL2_FMO == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__55 : Bool)
                                      then
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                                      else
                                        (do
                                          let w__59 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       (EL2Enabled ())) : Bool)
                                                  then
                                                    (do
                                                      let w__57 ← (( do (ELUsingAArch32 EL2) ) :
                                                        SailM Bool )
                                                      (pure (((! w__57) : Bool))))
                                                  else (pure false)) && ((__HCR_EL2_IMO == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__59 : Bool)
                                          then
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL2
                                                (BitVec.toNat 0x03#8)))
                                          else
                                            (do
                                              let w__63 ← (( do
                                                (pure ((← do
                                                      if ((← do
                                                           (EL2Enabled ())) : Bool)
                                                      then
                                                        (do
                                                          (ELUsingAArch32 EL2))
                                                      else (pure false)) && ((__HCR_FMO == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__63 : Bool)
                                              then
                                                (do
                                                  (AArch32_TakeHypTrapException
                                                    (BitVec.toNat 0x03#8)))
                                              else
                                                (do
                                                  let w__67 ← (( do
                                                    (pure ((← do
                                                          if ((← do
                                                               (EL2Enabled ())) : Bool)
                                                          then
                                                            (do
                                                              (ELUsingAArch32 EL2))
                                                          else (pure false)) && ((__HCR_IMO == 1#1) : Bool)))
                                                    ) : SailM Bool )
                                                  if (w__67 : Bool)
                                                  then
                                                    (do
                                                      (AArch32_TakeHypTrapException
                                                        (BitVec.toNat 0x03#8)))
                                                  else
                                                    (do
                                                      let w__72 ← (( do
                                                        if ((← do
                                                             if (((HaveEL EL3) : Bool) : Bool)
                                                             then
                                                               (do
                                                                 let w__68 ← (( do
                                                                   (ELUsingAArch32 EL3) ) : SailM
                                                                   Bool )
                                                                 (pure (((! w__68) : Bool))))
                                                             else (pure false)) : Bool)
                                                        then
                                                          (do
                                                            let w__70 ← (( do readReg SCR_EL3 ) :
                                                              SailM (BitVec 64) )
                                                            let w__71 ← (( do readReg SCR_EL3 ) :
                                                              SailM (BitVec 64) )
                                                            (pure (((((_get_SCR_EL3_Type_IRQ w__70) +++ (_get_SCR_EL3_Type_FIQ
                                                                    w__71)) == 0b11#2) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__72 : Bool)
                                                      then
                                                        (do
                                                          let w__75 ← (( do
                                                            if ((← do
                                                                 (Halted ())) : Bool)
                                                            then
                                                              (do
                                                                let w__74 ← (( do (EDSCR_read ())
                                                                  ) : SailM (BitVec 32) )
                                                                (pure ((((_get_EDSCR_Type_SDD w__74) == 1#1) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__75 : Bool)
                                                          then sailThrow ((Error_Undefined ()))
                                                          else
                                                            (do
                                                              (AArch64_AArch32SystemAccessTrap EL3
                                                                (BitVec.toNat 0x03#8))))
                                                      else
                                                        (do
                                                          let w__81 ← (( do
                                                            if ((← do
                                                                 (pure ((← do
                                                                       if (((HaveEL EL3) : Bool) : Bool)
                                                                       then
                                                                         (do
                                                                           (ELUsingAArch32 EL3))
                                                                       else (pure false)) && ((__PSTATE_M != M32_Monitor) : Bool)))) : Bool)
                                                            then
                                                              (do
                                                                let w__79 ← (( do readReg SCR ) :
                                                                  SailM (BitVec 32) )
                                                                let w__80 ← (( do readReg SCR ) :
                                                                  SailM (BitVec 32) )
                                                                (pure (((((_get_SCR_Type_IRQ w__79) +++ (_get_SCR_Type_FIQ
                                                                        w__80)) == 0b11#2) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__81 : Bool)
                                                          then
                                                            (do
                                                              let w__84 ← (( do
                                                                if ((← do
                                                                     (Halted ())) : Bool)
                                                                then
                                                                  (do
                                                                    let w__83 ← (( do
                                                                      (EDSCR_read ()) ) : SailM
                                                                      (BitVec 32) )
                                                                    (pure ((((_get_EDSCR_Type_SDD
                                                                          w__83) == 1#1) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__84 : Bool)
                                                              then sailThrow ((Error_Undefined ()))
                                                              else
                                                                (do
                                                                  (AArch32_TakeMonitorTrapException
                                                                    ())))
                                                          else
                                                            (do
                                                              let w__85 ← (( do (R_read t2) ) :
                                                                SailM (BitVec 32) )
                                                              let w__86 ← (( do (R_read t) ) :
                                                                SailM (BitVec 32) )
                                                              (ICC_SGI1R_write
                                                                (Mk_ICC_SGI1R_Type (w__85 +++ w__86)))))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__97 ← (( do
                if ((← do
                     if ((← do
                          if ((← do
                               if ((← do
                                    (pure ((← do
                                          (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
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
                         let w__93 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                         (pure (((! w__93) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__95 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    let w__96 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    (pure (((((_get_SCR_EL3_Type_IRQ w__95) +++ (_get_SCR_EL3_Type_FIQ w__96)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__97 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__108 ← (( do
                    if ((← do
                         if ((← do
                              if ((← do
                                   if ((← do
                                        (pure ((← do
                                              (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                   then
                                     (do
                                       let w__100 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                       (pure ((((_get_EDSCR_Type_SDD w__100) == 1#1) : Bool))))
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
                        let w__106 ← (( do readReg SCR ) : SailM (BitVec 32) )
                        let w__107 ← (( do readReg SCR ) : SailM (BitVec 32) )
                        (pure (((((_get_SCR_Type_IRQ w__106) +++ (_get_SCR_Type_FIQ w__107)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__108 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__ICC_HSRE_SRE == 0#1) : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__113 ← (( do
                            if ((← do
                                 if (((HaveEL EL3) : Bool) : Bool)
                                 then
                                   (do
                                     let w__109 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                     (pure (((! w__109) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__111 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                let w__112 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                (pure (((((_get_SCR_EL3_Type_IRQ w__111) +++ (_get_SCR_EL3_Type_FIQ
                                        w__112)) == 0b11#2) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__113 : Bool)
                          then
                            (do
                              let w__116 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__115 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__115) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__116 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                          else
                            (do
                              let w__121 ← (( do
                                if ((← do
                                     if (((HaveEL EL3) : Bool) : Bool)
                                     then
                                       (do
                                         (ELUsingAArch32 EL3))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__119 ← (( do readReg SCR ) : SailM (BitVec 32) )
                                    let w__120 ← (( do readReg SCR ) : SailM (BitVec 32) )
                                    (pure (((((_get_SCR_Type_IRQ w__119) +++ (_get_SCR_Type_FIQ
                                            w__120)) == 0b11#2) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__121 : Bool)
                              then
                                (do
                                  let w__124 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__123 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__123) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__124 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch32_TakeMonitorTrapException ())))
                              else
                                (do
                                  let w__125 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                                  let w__126 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (ICC_SGI1R_write (Mk_ICC_SGI1R_Type (w__125 +++ w__126)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__127 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                      let w__128 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (ICC_SGI1R_write (Mk_ICC_SGI1R_Type (w__127 +++ w__128)))))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def PAR_SysRegWrite64_867d7cbf8d644296 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T7 : (BitVec 1) := (_get_HSTR_EL2_Type_T7 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T7 : (BitVec 1) := (_get_HSTR_Type_T7 w__2)
  let w__3 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__7 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__5 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__5) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
          else
            (do
              let w__11 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
              if (w__11 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
              else
                (do
                  let w__13 ← (( do
                    if (((HaveEL EL3) : Bool) : Bool)
                    then
                      (do
                        (ELUsingAArch32 EL3))
                    else (pure false) ) : SailM Bool )
                  if (w__13 : Bool)
                  then
                    (do
                      let w__14 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                      let w__15 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      writeReg PAR_NS (Mk_PAR_Type (w__14 +++ w__15)))
                  else
                    (do
                      let w__16 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                      let w__17 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (PAR_write (Mk_PAR_Type (w__16 +++ w__17)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__19 ← (( do
                if (((HaveEL EL3) : Bool) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__19 : Bool)
              then
                (do
                  let w__20 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                  let w__21 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  writeReg PAR_NS (Mk_PAR_Type (w__20 +++ w__21)))
              else
                (do
                  let w__22 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                  let w__23 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (PAR_write (Mk_PAR_Type (w__22 +++ w__23)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then
                    (do
                      let w__24 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                      let w__25 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      writeReg PAR_S (Mk_PAR_Type (w__24 +++ w__25)))
                  else
                    (do
                      let w__26 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                      let w__27 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      writeReg PAR_NS (Mk_PAR_Type (w__26 +++ w__27))))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def PMCCNTR_SysRegWrite64_51a4ab1690d771a1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TPM : (BitVec 1) := (_get_MDCR_EL3_Type_TPM w__1)
  let w__2 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
  let __PMUSERENR_EL0_EN : (BitVec 1) := (_get_PMUSERENR_EL0_Type_EN w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__3)
  let w__4 ← (( do (PMUSERENR_read ()) ) : SailM (BitVec 32) )
  let __PMUSERENR_EN : (BitVec 1) := (_get_PMUSERENR_Type_EN w__4)
  let w__5 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TGE : (BitVec 1) := (_get_HCR_Type_TGE w__5)
  let w__6 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T9 : (BitVec 1) := (_get_HSTR_EL2_Type_T9 w__6)
  let w__7 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T9 : (BitVec 1) := (_get_HSTR_Type_T9 w__7)
  let w__8 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__8)
  let w__9 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR_EL2_PMCCNTR_EL0 : (BitVec 1) := (_get_HDFGWTR_EL2_Type_PMCCNTR_EL0 w__9)
  let w__10 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TPM : (BitVec 1) := (_get_MDCR_EL2_Type_TPM w__10)
  let w__11 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  let __HDCR_TPM : (BitVec 1) := (_get_HDCR_Type_TPM w__11)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__20 ← (( do
        (pure ((← do
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
              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
      if (w__20 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__29 ← (( do
            if ((← do
                 let w__21 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                 (pure (((! w__21) : Bool)))) : Bool)
            then
              (do
                if ((← do
                     if ((← do
                          (IsFeatureImplemented FEAT_PMUv3p9)) : Bool)
                     then
                       (do
                         let w__23 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         let w__24 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         (pure (((((_get_PMUSERENR_EL0_Type_UEN w__23) +++ (_get_PMUSERENR_EL0_Type_EN
                                 w__24)) == 0b00#2) : Bool))))
                     else (pure false)) : Bool)
                then (pure true)
                else
                  (do
                    (pure ((← do
                          let w__26 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool )
                          (pure (((! w__26) : Bool)))) && ((__PMUSERENR_EL0_EN == 0#1) : Bool)))))
            else (pure false) ) : SailM Bool )
          if (w__29 : Bool)
          then
            (do
              let w__33 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__31 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__31) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__33 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
              else
                (do
                  (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8))))
          else
            (do
              let w__35 ← (( do
                (pure ((← do
                      (ELUsingAArch32 EL1)) && ((__PMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool )
              if (w__35 : Bool)
              then
                (do
                  let w__39 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__37 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__37) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__39 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__43 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                      if (w__43 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                      else sailThrow ((Error_Undefined ()))))
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
                                      w__48)) != 0b11#2) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T9 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__50 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__54 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HSTR_T9 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__54 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__64 ← (( do
                            (pure ((← do
                                  (pure ((← do
                                        if ((← do
                                             if ((← do
                                                  if ((← do
                                                       (EL2Enabled ())) : Bool)
                                                  then
                                                    (do
                                                      let w__56 ← (( do (ELUsingAArch32 EL1) ) :
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
                                                         w__59)) != 0b11#2) : Bool))))
                                             else (pure false)) : Bool)
                                        then
                                          (do
                                            (IsFeatureImplemented FEAT_FGT))
                                        else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HDFGWTR_EL2_PMCCNTR_EL0 == 1#1) : Bool)))
                            ) : SailM Bool )
                          if (w__64 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                          else
                            (do
                              let w__68 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          let w__66 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                          (pure (((! w__66) : Bool))))
                                      else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__68 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                              else
                                (do
                                  let w__72 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (EL2Enabled ())) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL2))
                                          else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__72 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      let w__75 ← (( do
                                        (pure ((← do
                                              if (((HaveEL EL3) : Bool) : Bool)
                                              then
                                                (do
                                                  let w__73 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                    Bool )
                                                  (pure (((! w__73) : Bool))))
                                              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__75 : Bool)
                                      then
                                        (do
                                          let w__78 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__77 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__77) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__78 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x04#8))))
                                      else
                                        (do
                                          let w__79 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                                          let w__80 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                          (PMCCNTR_write (Mk_PMCCNTR_Type (w__79 +++ w__80)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
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
                      let w__87 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__87) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
          if (w__89 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__93 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__91 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__91) : Bool))))
                      else (pure false)) && ((__HSTR_EL2_T9 == 1#1) : Bool))) ) : SailM Bool )
              if (w__93 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
              else
                (do
                  let w__97 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HSTR_T9 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__97 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__101 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__99 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__99) : Bool))))
                              else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__101 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__105 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__105 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                          else
                            (do
                              let w__108 ← (( do
                                (pure ((← do
                                      if (((HaveEL EL3) : Bool) : Bool)
                                      then
                                        (do
                                          let w__106 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__106) : Bool))))
                                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__108 : Bool)
                              then
                                (do
                                  let w__111 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__110 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__110) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__111 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                              else
                                (do
                                  let w__112 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                                  let w__113 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (PMCCNTR_write (Mk_PMCCNTR_Type (w__112 +++ w__113))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__122 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                then
                                  (do
                                    let w__116 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__116) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__120 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__120) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__122 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__125 ← (( do
                    (pure ((← do
                          if (((HaveEL EL3) : Bool) : Bool)
                          then
                            (do
                              let w__123 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__123) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
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
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                  else
                    (do
                      let w__129 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                      let w__130 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (PMCCNTR_write (Mk_PMCCNTR_Type (w__129 +++ w__130))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__131 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                  let w__132 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (PMCCNTR_write (Mk_PMCCNTR_Type (w__131 +++ w__132))))
              else (pure (())))))


end ArmFull.Functions
