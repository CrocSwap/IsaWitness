module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0035
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0054
public import ArmFull.Fn.M0055
public import ArmFull.Fn.M0056
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0070
public import ArmFull.Fn.M0081
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
def ICC_MSRE_SysRegWrite32_3238a1354a48916c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T12 : (BitVec 1) := (_get_HSTR_EL2_Type_T12 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T12 : (BitVec 1) := (_get_HSTR_Type_T12 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__6 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__4 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__4) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T12 == 1#1) : Bool))) ) : SailM Bool )
          if (w__6 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__10 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T12 == 1#1) : Bool))) ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__11 ← (( do readReg CP15SDISABLE2 ) : SailM Signal )
                  if ((BEq.beq w__11 Signal_High) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__12 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      writeReg ICC_MSRE (Mk_ICC_MSRE_Type w__12)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ICC_PMR_SysRegWrite32_b23a221ce6bd2853 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__23 ← (( do
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
              let w__36 ← (( do
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
                                         let w__27 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                         (pure ((((_get_EDSCR_Type_SDD w__27) == 1#1) : Bool))))
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
                    let w__34 ← (( do readReg SCR ) : SailM (BitVec 32) )
                    let w__35 ← (( do readReg SCR ) : SailM (BitVec 32) )
                    (pure (((((_get_SCR_Type_IRQ w__34) +++ (_get_SCR_Type_FIQ w__35)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__36 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__40 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__38 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__38) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T12 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__40 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__44 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HSTR_T12 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__44 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__48 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__46 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                      (pure (((! w__46) : Bool))))
                                  else (pure false)) && ((__ICH_HCR_EL2_TC == 1#1) : Bool))) ) :
                            SailM Bool )
                          if (w__48 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__52 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__ICH_HCR_TC == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__52 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__56 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (EL2Enabled ())) : Bool)
                                          then
                                            (do
                                              let w__54 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                Bool )
                                              (pure (((! w__54) : Bool))))
                                          else (pure false)) && ((__HCR_EL2_FMO == 1#1) : Bool))) )
                                    : SailM Bool )
                                  if (w__56 : Bool)
                                  then
                                    (do
                                      let w__57 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      (ICV_PMR_write (Mk_ICV_PMR_Type w__57)))
                                  else
                                    (do
                                      let w__61 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (EL2Enabled ())) : Bool)
                                              then
                                                (do
                                                  let w__59 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                    Bool )
                                                  (pure (((! w__59) : Bool))))
                                              else (pure false)) && ((__HCR_EL2_IMO == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__61 : Bool)
                                      then
                                        (do
                                          let w__62 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                          (ICV_PMR_write (Mk_ICV_PMR_Type w__62)))
                                      else
                                        (do
                                          let w__66 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       (EL2Enabled ())) : Bool)
                                                  then
                                                    (do
                                                      (ELUsingAArch32 EL2))
                                                  else (pure false)) && ((__HCR_FMO == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__66 : Bool)
                                          then
                                            (do
                                              let w__67 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                              (ICV_PMR_write (Mk_ICV_PMR_Type w__67)))
                                          else
                                            (do
                                              let w__71 ← (( do
                                                (pure ((← do
                                                      if ((← do
                                                           (EL2Enabled ())) : Bool)
                                                      then
                                                        (do
                                                          (ELUsingAArch32 EL2))
                                                      else (pure false)) && ((__HCR_IMO == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__71 : Bool)
                                              then
                                                (do
                                                  let w__72 ← (( do (R_read t) ) : SailM
                                                    (BitVec 32) )
                                                  (ICV_PMR_write (Mk_ICV_PMR_Type w__72)))
                                              else
                                                (do
                                                  let w__78 ← (( do
                                                    if ((← do
                                                         if ((← do
                                                              (HaveEL EL3)) : Bool)
                                                         then
                                                           (do
                                                             let w__74 ← (( do
                                                               (ELUsingAArch32 EL3) ) : SailM Bool )
                                                             (pure (((! w__74) : Bool))))
                                                         else (pure false)) : Bool)
                                                    then
                                                      (do
                                                        let w__76 ← (( do readReg SCR_EL3 ) :
                                                          SailM (BitVec 64) )
                                                        let w__77 ← (( do readReg SCR_EL3 ) :
                                                          SailM (BitVec 64) )
                                                        (pure (((((_get_SCR_EL3_Type_IRQ w__76) +++ (_get_SCR_EL3_Type_FIQ
                                                                w__77)) == 0b11#2) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__78 : Bool)
                                                  then
                                                    (do
                                                      let w__81 ← (( do
                                                        if ((← do
                                                             (Halted ())) : Bool)
                                                        then
                                                          (do
                                                            let w__80 ← (( do (EDSCR_read ()) ) :
                                                              SailM (BitVec 32) )
                                                            (pure ((((_get_EDSCR_Type_SDD w__80) == 1#1) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__81 : Bool)
                                                      then sailThrow ((Error_Undefined ()))
                                                      else
                                                        (do
                                                          (AArch64_AArch32SystemAccessTrap EL3
                                                            (BitVec.toNat 0x03#8))))
                                                  else
                                                    (do
                                                      let w__88 ← (( do
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
                                                            let w__86 ← (( do readReg SCR ) :
                                                              SailM (BitVec 32) )
                                                            let w__87 ← (( do readReg SCR ) :
                                                              SailM (BitVec 32) )
                                                            (pure (((((_get_SCR_Type_IRQ w__86) +++ (_get_SCR_Type_FIQ
                                                                    w__87)) == 0b11#2) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__88 : Bool)
                                                      then
                                                        (do
                                                          let w__91 ← (( do
                                                            if ((← do
                                                                 (Halted ())) : Bool)
                                                            then
                                                              (do
                                                                let w__90 ← (( do (EDSCR_read ())
                                                                  ) : SailM (BitVec 32) )
                                                                (pure ((((_get_EDSCR_Type_SDD w__90) == 1#1) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__91 : Bool)
                                                          then sailThrow ((Error_Undefined ()))
                                                          else
                                                            (do
                                                              (AArch32_TakeMonitorTrapException ())))
                                                      else
                                                        (do
                                                          let w__92 ← (( do (R_read t) ) : SailM
                                                            (BitVec 32) )
                                                          (ICC_PMR_write (Mk_ICC_PMR_Type w__92)))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__104 ← (( do
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
                                   let w__96 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                   (pure ((((_get_EDSCR_Type_SDD w__96) == 1#1) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) : Bool)
                     then
                       (do
                         let w__100 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                         (pure (((! w__100) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__102 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    let w__103 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    (pure (((((_get_SCR_EL3_Type_IRQ w__102) +++ (_get_SCR_EL3_Type_FIQ w__103)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__104 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__116 ← (( do
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
                                       let w__108 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                       (pure ((((_get_EDSCR_Type_SDD w__108) == 1#1) : Bool))))
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
                        let w__114 ← (( do readReg SCR ) : SailM (BitVec 32) )
                        let w__115 ← (( do readReg SCR ) : SailM (BitVec 32) )
                        (pure (((((_get_SCR_Type_IRQ w__114) +++ (_get_SCR_Type_FIQ w__115)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__116 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__ICC_HSRE_SRE == 0#1) : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__122 ← (( do
                            if ((← do
                                 if ((← do
                                      (HaveEL EL3)) : Bool)
                                 then
                                   (do
                                     let w__118 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                     (pure (((! w__118) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__120 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                let w__121 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                (pure (((((_get_SCR_EL3_Type_IRQ w__120) +++ (_get_SCR_EL3_Type_FIQ
                                        w__121)) == 0b11#2) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__122 : Bool)
                          then
                            (do
                              let w__125 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__124 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__124) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__125 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                          else
                            (do
                              let w__131 ← (( do
                                if ((← do
                                     if ((← do
                                          (HaveEL EL3)) : Bool)
                                     then
                                       (do
                                         (ELUsingAArch32 EL3))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__129 ← (( do readReg SCR ) : SailM (BitVec 32) )
                                    let w__130 ← (( do readReg SCR ) : SailM (BitVec 32) )
                                    (pure (((((_get_SCR_Type_IRQ w__129) +++ (_get_SCR_Type_FIQ
                                            w__130)) == 0b11#2) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__131 : Bool)
                              then
                                (do
                                  let w__134 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__133 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__133) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__134 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch32_TakeMonitorTrapException ())))
                              else
                                (do
                                  let w__135 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (ICC_PMR_write (Mk_ICC_PMR_Type w__135))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__ICC_MSRE_SRE == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__136 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (ICC_PMR_write (Mk_ICC_PMR_Type w__136))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ICC_SRE_SysRegWrite32_9b4f583336a77d42 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL3_Enable : (BitVec 1) := (_get_ICC_SRE_EL3_Type_Enable w__1)
  let w__2 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T12 : (BitVec 1) := (_get_HSTR_EL2_Type_T12 w__2)
  let w__3 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T12 : (BitVec 1) := (_get_HSTR_Type_T12 w__3)
  let w__4 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL2_Enable : (BitVec 1) := (_get_ICC_SRE_EL2_Type_Enable w__4)
  let w__5 ← (( do (ICC_HSRE_read ()) ) : SailM (BitVec 32) )
  let __ICC_HSRE_Enable : (BitVec 1) := (_get_ICC_HSRE_Type_Enable w__5)
  let w__6 ← (( do readReg ICC_MSRE ) : SailM (BitVec 32) )
  let __ICC_MSRE_Enable : (BitVec 1) := (_get_ICC_MSRE_Type_Enable w__6)
  let w__7 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NS : (BitVec 1) := (_get_SCR_EL3_Type_NS w__7)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__17 ← (( do
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
                                let w__11 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__11) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__15 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__15) : Bool))))
                  else (pure false)) && ((__ICC_SRE_EL3_Enable == 0#1) : Bool))) ) : SailM Bool )
          if (w__17 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__21 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__19 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__19) : Bool))))
                      else (pure false)) && ((__HSTR_EL2_T12 == 1#1) : Bool))) ) : SailM Bool )
              if (w__21 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__25 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HSTR_T12 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__25 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__29 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__27 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__27) : Bool))))
                              else (pure false)) && ((__ICC_SRE_EL2_Enable == 0#1) : Bool))) ) :
                        SailM Bool )
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
                                  else (pure false)) && ((__ICC_HSRE_Enable == 0#1) : Bool))) ) :
                            SailM Bool )
                          if (w__33 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__37 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL3))
                                      else (pure false)) && ((__ICC_MSRE_Enable == 0#1) : Bool))) )
                                : SailM Bool )
                              if (w__37 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  let w__41 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (HaveEL EL3)) : Bool)
                                          then
                                            (do
                                              let w__39 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                Bool )
                                              (pure (((! w__39) : Bool))))
                                          else (pure false)) && ((__ICC_SRE_EL3_Enable == 0#1) : Bool)))
                                    ) : SailM Bool )
                                  if (w__41 : Bool)
                                  then
                                    (do
                                      let w__44 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__43 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__43) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__44 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                                  else
                                    (do
                                      let w__45 ← (( do (HaveEL EL3) ) : SailM Bool )
                                      if (w__45 : Bool)
                                      then
                                        (do
                                          if ((__SCR_EL3_NS == 0#1) : Bool)
                                          then
                                            (do
                                              let w__46 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                              (ICC_SRE_S_write (Mk_ICC_SRE_Type w__46)))
                                          else
                                            (do
                                              let w__47 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                              (ICC_SRE_NS_write (Mk_ICC_SRE_Type w__47))))
                                      else
                                        (do
                                          let w__48 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                          (ICC_SRE_write (Mk_ICC_SRE_Type w__48)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__58 ← (( do
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
                                    let w__52 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__52) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__56 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__56) : Bool))))
                      else (pure false)) && ((__ICC_SRE_EL3_Enable == 0#1) : Bool))) ) : SailM Bool
                )
              if (w__58 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__62 ← (( do
                    (pure ((← do
                          if ((← do
                               (HaveEL EL3)) : Bool)
                          then
                            (do
                              let w__60 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__60) : Bool))))
                          else (pure false)) && ((__ICC_SRE_EL3_Enable == 0#1) : Bool))) ) : SailM
                    Bool )
                  if (w__62 : Bool)
                  then
                    (do
                      let w__65 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__64 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__64) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__65 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                  else
                    (do
                      if ((__ICC_MSRE_Enable == 0#1) : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__66 ← (( do (HaveEL EL3) ) : SailM Bool )
                          if (w__66 : Bool)
                          then
                            (do
                              if ((__SCR_EL3_NS == 0#1) : Bool)
                              then
                                (do
                                  let w__67 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (ICC_SRE_S_write (Mk_ICC_SRE_Type w__67)))
                              else
                                (do
                                  let w__68 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (ICC_SRE_NS_write (Mk_ICC_SRE_Type w__68))))
                          else
                            (do
                              let w__69 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (ICC_SRE_write (Mk_ICC_SRE_Type w__69)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_NS == 0#1) : Bool)
                  then
                    (do
                      let w__70 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (ICC_SRE_S_write (Mk_ICC_SRE_Type w__70)))
                  else
                    (do
                      let w__71 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (ICC_SRE_NS_write (Mk_ICC_SRE_Type w__71))))
              else (pure (())))))


end ArmFull.Functions
