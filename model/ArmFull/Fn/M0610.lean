module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0035
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0054
public import ArmFull.Fn.M0055
public import ArmFull.Fn.M0056
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0063
public import ArmFull.Fn.M0064
public import ArmFull.Fn.M0070
public import ArmFull.Fn.M0073
public import ArmFull.Fn.M0092
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
          let w__24 ← (( do
            if ((← do
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
                 else (pure false)) : Bool)
            then
              (do
                let w__22 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                let w__23 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                (pure (((((_get_SCR_EL3_Type_IRQ w__22) +++ (_get_SCR_EL3_Type_FIQ w__23)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__24 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__37 ← (( do
                if ((← do
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
                                         let w__28 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                         (pure ((((_get_EDSCR_Type_SDD w__28) == 1#1) : Bool))))
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
                    let w__35 ← (( do readReg SCR ) : SailM (BitVec 32) )
                    let w__36 ← (( do readReg SCR ) : SailM (BitVec 32) )
                    (pure (((((_get_SCR_Type_IRQ w__35) +++ (_get_SCR_Type_FIQ w__36)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__37 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__41 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__39 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__39) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T12 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__41 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__45 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HSTR_T12 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__45 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          if ((__ICC_SRE_SRE == 0#1) : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              let w__49 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          let w__47 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                          (pure (((! w__47) : Bool))))
                                      else (pure false)) && ((__ICH_HCR_EL2_TC == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__49 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__53 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (EL2Enabled ())) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL2))
                                          else (pure false)) && ((__ICH_HCR_TC == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__53 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      let w__57 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (EL2Enabled ())) : Bool)
                                              then
                                                (do
                                                  let w__55 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                    Bool )
                                                  (pure (((! w__55) : Bool))))
                                              else (pure false)) && ((__HCR_EL2_FMO == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__57 : Bool)
                                      then
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                                      else
                                        (do
                                          let w__61 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       (EL2Enabled ())) : Bool)
                                                  then
                                                    (do
                                                      let w__59 ← (( do (ELUsingAArch32 EL2) ) :
                                                        SailM Bool )
                                                      (pure (((! w__59) : Bool))))
                                                  else (pure false)) && ((__HCR_EL2_IMO == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__61 : Bool)
                                          then
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL2
                                                (BitVec.toNat 0x03#8)))
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
                                                  (AArch32_TakeHypTrapException
                                                    (BitVec.toNat 0x03#8)))
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
                                                      (AArch32_TakeHypTrapException
                                                        (BitVec.toNat 0x03#8)))
                                                  else
                                                    (do
                                                      let w__75 ← (( do
                                                        if ((← do
                                                             if ((← do
                                                                  (HaveEL EL3)) : Bool)
                                                             then
                                                               (do
                                                                 let w__71 ← (( do
                                                                   (ELUsingAArch32 EL3) ) : SailM
                                                                   Bool )
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
                                                                let w__77 ← (( do (EDSCR_read ())
                                                                  ) : SailM (BitVec 32) )
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
                                                          let w__85 ← (( do
                                                            if ((← do
                                                                 (pure ((← do
                                                                       if ((← do
                                                                            (HaveEL EL3)) : Bool)
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
                                                                    let w__87 ← (( do
                                                                      (EDSCR_read ()) ) : SailM
                                                                      (BitVec 32) )
                                                                    (pure ((((_get_EDSCR_Type_SDD
                                                                          w__87) == 1#1) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__88 : Bool)
                                                              then sailThrow ((Error_Undefined ()))
                                                              else
                                                                (do
                                                                  (AArch32_TakeMonitorTrapException
                                                                    ())))
                                                          else
                                                            (do
                                                              let w__89 ← (( do (R_read t2) ) :
                                                                SailM (BitVec 32) )
                                                              let w__90 ← (( do (R_read t) ) :
                                                                SailM (BitVec 32) )
                                                              (ICC_SGI1R_write
                                                                (Mk_ICC_SGI1R_Type (w__89 +++ w__90)))))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__102 ← (( do
                if ((← do
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
                                   let w__94 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                   (pure ((((_get_EDSCR_Type_SDD w__94) == 1#1) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) : Bool)
                     then
                       (do
                         let w__98 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                         (pure (((! w__98) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__100 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    let w__101 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    (pure (((((_get_SCR_EL3_Type_IRQ w__100) +++ (_get_SCR_EL3_Type_FIQ w__101)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__102 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__114 ← (( do
                    if ((← do
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
                                       let w__106 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                       (pure ((((_get_EDSCR_Type_SDD w__106) == 1#1) : Bool))))
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
                        let w__112 ← (( do readReg SCR ) : SailM (BitVec 32) )
                        let w__113 ← (( do readReg SCR ) : SailM (BitVec 32) )
                        (pure (((((_get_SCR_Type_IRQ w__112) +++ (_get_SCR_Type_FIQ w__113)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__114 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__ICC_HSRE_SRE == 0#1) : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__120 ← (( do
                            if ((← do
                                 if ((← do
                                      (HaveEL EL3)) : Bool)
                                 then
                                   (do
                                     let w__116 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                     (pure (((! w__116) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__118 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                let w__119 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                (pure (((((_get_SCR_EL3_Type_IRQ w__118) +++ (_get_SCR_EL3_Type_FIQ
                                        w__119)) == 0b11#2) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__120 : Bool)
                          then
                            (do
                              let w__123 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__122 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__122) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__123 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                          else
                            (do
                              let w__129 ← (( do
                                if ((← do
                                     if ((← do
                                          (HaveEL EL3)) : Bool)
                                     then
                                       (do
                                         (ELUsingAArch32 EL3))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__127 ← (( do readReg SCR ) : SailM (BitVec 32) )
                                    let w__128 ← (( do readReg SCR ) : SailM (BitVec 32) )
                                    (pure (((((_get_SCR_Type_IRQ w__127) +++ (_get_SCR_Type_FIQ
                                            w__128)) == 0b11#2) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__129 : Bool)
                              then
                                (do
                                  let w__132 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__131 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__131) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__132 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch32_TakeMonitorTrapException ())))
                              else
                                (do
                                  let w__133 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                                  let w__134 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (ICC_SGI1R_write (Mk_ICC_SGI1R_Type (w__133 +++ w__134)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__135 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                      let w__136 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (ICC_SGI1R_write (Mk_ICC_SGI1R_Type (w__135 +++ w__136)))))
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
                  let w__14 ← (( do
                    if ((← do
                         (HaveEL EL3)) : Bool)
                    then
                      (do
                        (ELUsingAArch32 EL3))
                    else (pure false) ) : SailM Bool )
                  if (w__14 : Bool)
                  then
                    (do
                      let w__15 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                      let w__16 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      writeReg PAR_NS (Mk_PAR_Type (w__15 +++ w__16)))
                  else
                    (do
                      let w__17 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                      let w__18 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (PAR_write (Mk_PAR_Type (w__17 +++ w__18)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__21 ← (( do
                if ((← do
                     (HaveEL EL3)) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__21 : Bool)
              then
                (do
                  let w__22 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                  let w__23 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  writeReg PAR_NS (Mk_PAR_Type (w__22 +++ w__23)))
              else
                (do
                  let w__24 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                  let w__25 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (PAR_write (Mk_PAR_Type (w__24 +++ w__25)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then
                    (do
                      let w__26 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                      let w__27 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      writeReg PAR_S (Mk_PAR_Type (w__26 +++ w__27)))
                  else
                    (do
                      let w__28 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                      let w__29 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      writeReg PAR_NS (Mk_PAR_Type (w__28 +++ w__29))))
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
      let w__21 ← (( do
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
              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
      if (w__21 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__30 ← (( do
            if ((← do
                 let w__22 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                 (pure (((! w__22) : Bool)))) : Bool)
            then
              (do
                if ((← do
                     if ((← do
                          (IsFeatureImplemented FEAT_PMUv3p9)) : Bool)
                     then
                       (do
                         let w__24 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         let w__25 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         (pure (((((_get_PMUSERENR_EL0_Type_UEN w__24) +++ (_get_PMUSERENR_EL0_Type_EN
                                 w__25)) == 0b00#2) : Bool))))
                     else (pure false)) : Bool)
                then (pure true)
                else
                  (do
                    (pure ((← do
                          let w__27 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool )
                          (pure (((! w__27) : Bool)))) && ((__PMUSERENR_EL0_EN == 0#1) : Bool)))))
            else (pure false) ) : SailM Bool )
          if (w__30 : Bool)
          then
            (do
              let w__34 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__32 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__32) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__34 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
              else
                (do
                  (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x04#8))))
          else
            (do
              let w__36 ← (( do
                (pure ((← do
                      (ELUsingAArch32 EL1)) && ((__PMUSERENR_EN == 0#1) : Bool))) ) : SailM Bool )
              if (w__36 : Bool)
              then
                (do
                  let w__40 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__38 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__38) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__40 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__44 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TGE == 1#1) : Bool))) ) : SailM Bool )
                      if (w__44 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                      else sailThrow ((Error_Undefined ()))))
              else
                (do
                  let w__51 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   let w__46 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                   (pure (((! w__46) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__48 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__49 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__48) +++ (_get_HCR_EL2_Type_TGE
                                      w__49)) != 0b11#2) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T9 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__51 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__55 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HSTR_T9 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__55 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__67 ← (( do
                            (pure ((← do
                                  if ((← do
                                       if ((← do
                                            if ((← do
                                                 if ((← do
                                                      (EL2Enabled ())) : Bool)
                                                 then
                                                   (do
                                                     let w__57 ← (( do (ELUsingAArch32 EL1) ) :
                                                       SailM Bool )
                                                     (pure (((! w__57) : Bool))))
                                                 else (pure false)) : Bool)
                                            then
                                              (do
                                                let w__59 ← (( do readReg HCR_EL2 ) : SailM
                                                  (BitVec 64) )
                                                let w__60 ← (( do readReg HCR_EL2 ) : SailM
                                                  (BitVec 64) )
                                                (pure (((((_get_HCR_EL2_Type_E2H w__59) +++ (_get_HCR_EL2_Type_TGE
                                                        w__60)) != 0b11#2) : Bool))))
                                            else (pure false)) : Bool)
                                       then
                                         (do
                                           (IsFeatureImplemented FEAT_FGT))
                                       else (pure false)) : Bool)
                                  then
                                    (do
                                      (pure ((← do
                                            let w__64 ← (( do (HaveEL EL3) ) : SailM Bool )
                                            (pure (((! w__64) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                                  else (pure false)) && ((__HDFGWTR_EL2_PMCCNTR_EL0 == 1#1) : Bool)))
                            ) : SailM Bool )
                          if (w__67 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                          else
                            (do
                              let w__71 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          let w__69 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                          (pure (((! w__69) : Bool))))
                                      else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__71 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                              else
                                (do
                                  let w__75 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (EL2Enabled ())) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL2))
                                          else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__75 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                                  else
                                    (do
                                      let w__79 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (HaveEL EL3)) : Bool)
                                              then
                                                (do
                                                  let w__77 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                    Bool )
                                                  (pure (((! w__77) : Bool))))
                                              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__79 : Bool)
                                      then
                                        (do
                                          let w__82 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__81 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__81) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__82 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x04#8))))
                                      else
                                        (do
                                          let w__83 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                                          let w__84 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                          (PMCCNTR_write (Mk_PMCCNTR_Type (w__83 +++ w__84)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__94 ← (( do
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
                                let w__88 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__88) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__92 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__92) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
          if (w__94 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__98 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__96 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__96) : Bool))))
                      else (pure false)) && ((__HSTR_EL2_T9 == 1#1) : Bool))) ) : SailM Bool )
              if (w__98 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
              else
                (do
                  let w__102 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HSTR_T9 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__102 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                  else
                    (do
                      let w__106 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__104 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__104) : Bool))))
                              else (pure false)) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__106 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
                      else
                        (do
                          let w__110 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HDCR_TPM == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__110 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
                          else
                            (do
                              let w__114 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          let w__112 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__112) : Bool))))
                                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__114 : Bool)
                              then
                                (do
                                  let w__117 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__116 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__116) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__117 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                              else
                                (do
                                  let w__118 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                                  let w__119 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (PMCCNTR_write (Mk_PMCCNTR_Type (w__118 +++ w__119))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__129 ← (( do
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
                                    let w__123 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__123) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__127 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__127) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__129 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__133 ← (( do
                    (pure ((← do
                          if ((← do
                               (HaveEL EL3)) : Bool)
                          then
                            (do
                              let w__131 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__131) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__133 : Bool)
                  then
                    (do
                      let w__136 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__135 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__135) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__136 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x04#8))))
                  else
                    (do
                      let w__137 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                      let w__138 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (PMCCNTR_write (Mk_PMCCNTR_Type (w__137 +++ w__138))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__139 ← (( do (R_read t2) ) : SailM (BitVec 32) )
                  let w__140 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (PMCCNTR_write (Mk_PMCCNTR_Type (w__139 +++ w__140))))
              else (pure (())))))


end ArmFull.Functions
