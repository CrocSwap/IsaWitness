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
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0070
public import ArmFull.Fn.M0075
public import ArmFull.Fn.M0081
public import ArmFull.Fn.M0082
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0140
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0199
public import ArmFull.Fn.M0200
public import ArmFull.Fn.M0202
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
def ICV_AP1R_SysRegRead32_f50b3adcd6cb4d7f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                          let w__55 ← (( do (ICV_AP1R_read 0) ) : SailM
                                            (BitVec 32) )
                                          (R_set t w__55))
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
                                              let w__60 ← (( do (ICV_AP1R_read 0) ) : SailM
                                                (BitVec 32) )
                                              (R_set t w__60))
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
                                                          let w__77 ← (( do (ICC_AP1R_NS_read 0) )
                                                            : SailM (BitVec 32) )
                                                          (R_set t w__77))
                                                      else
                                                        (do
                                                          let w__78 ← (( do (ICC_AP1R_read 0) ) :
                                                            SailM (BitVec 32) )
                                                          (R_set t w__78))))))))))))))
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
                                      let w__114 ← (( do (ICC_AP1R_NS_read 0) ) : SailM
                                        (BitVec 32) )
                                      (R_set t w__114))
                                  else
                                    (do
                                      let w__115 ← (( do (ICC_AP1R_read 0) ) : SailM (BitVec 32) )
                                      (R_set t w__115))))))))
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
                          let w__116 ← (( do (ICC_AP1R_S_read 0) ) : SailM (BitVec 32) )
                          (R_set t w__116))
                      else
                        (do
                          let w__117 ← (( do (ICC_AP1R_NS_read 0) ) : SailM (BitVec 32) )
                          (R_set t w__117))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ICV_CTLR_SysRegRead32_084685ae7c38b87e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                                          else (pure false)) && ((__HCR_EL2_FMO == 1#1) : Bool))) )
                                    : SailM Bool )
                                  if (w__57 : Bool)
                                  then
                                    (do
                                      let w__58 ← (( do (ICV_CTLR_read ()) ) : SailM (BitVec 32) )
                                      (R_set t (__get_ICV_CTLR w__58)))
                                  else
                                    (do
                                      let w__62 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (EL2Enabled ())) : Bool)
                                              then
                                                (do
                                                  let w__60 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                    Bool )
                                                  (pure (((! w__60) : Bool))))
                                              else (pure false)) && ((__HCR_EL2_IMO == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__62 : Bool)
                                      then
                                        (do
                                          let w__63 ← (( do (ICV_CTLR_read ()) ) : SailM
                                            (BitVec 32) )
                                          (R_set t (__get_ICV_CTLR w__63)))
                                      else
                                        (do
                                          let w__67 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       (EL2Enabled ())) : Bool)
                                                  then
                                                    (do
                                                      (ELUsingAArch32 EL2))
                                                  else (pure false)) && ((__HCR_FMO == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__67 : Bool)
                                          then
                                            (do
                                              let w__68 ← (( do (ICV_CTLR_read ()) ) : SailM
                                                (BitVec 32) )
                                              (R_set t (__get_ICV_CTLR w__68)))
                                          else
                                            (do
                                              let w__72 ← (( do
                                                (pure ((← do
                                                      if ((← do
                                                           (EL2Enabled ())) : Bool)
                                                      then
                                                        (do
                                                          (ELUsingAArch32 EL2))
                                                      else (pure false)) && ((__HCR_IMO == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__72 : Bool)
                                              then
                                                (do
                                                  let w__73 ← (( do (ICV_CTLR_read ()) ) : SailM
                                                    (BitVec 32) )
                                                  (R_set t (__get_ICV_CTLR w__73)))
                                              else
                                                (do
                                                  let w__79 ← (( do
                                                    if ((← do
                                                         if ((← do
                                                              (HaveEL EL3)) : Bool)
                                                         then
                                                           (do
                                                             let w__75 ← (( do
                                                               (ELUsingAArch32 EL3) ) : SailM Bool )
                                                             (pure (((! w__75) : Bool))))
                                                         else (pure false)) : Bool)
                                                    then
                                                      (do
                                                        let w__77 ← (( do readReg SCR_EL3 ) :
                                                          SailM (BitVec 64) )
                                                        let w__78 ← (( do readReg SCR_EL3 ) :
                                                          SailM (BitVec 64) )
                                                        (pure (((((_get_SCR_EL3_Type_IRQ w__77) +++ (_get_SCR_EL3_Type_FIQ
                                                                w__78)) == 0b11#2) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__79 : Bool)
                                                  then
                                                    (do
                                                      let w__82 ← (( do
                                                        if ((← do
                                                             (Halted ())) : Bool)
                                                        then
                                                          (do
                                                            let w__81 ← (( do (EDSCR_read ()) ) :
                                                              SailM (BitVec 32) )
                                                            (pure ((((_get_EDSCR_Type_SDD w__81) == 1#1) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__82 : Bool)
                                                      then sailThrow ((Error_Undefined ()))
                                                      else
                                                        (do
                                                          (AArch64_AArch32SystemAccessTrap EL3
                                                            (BitVec.toNat 0x03#8))))
                                                  else
                                                    (do
                                                      let w__89 ← (( do
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
                                                            let w__87 ← (( do readReg SCR ) :
                                                              SailM (BitVec 32) )
                                                            let w__88 ← (( do readReg SCR ) :
                                                              SailM (BitVec 32) )
                                                            (pure (((((_get_SCR_Type_IRQ w__87) +++ (_get_SCR_Type_FIQ
                                                                    w__88)) == 0b11#2) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__89 : Bool)
                                                      then
                                                        (do
                                                          let w__92 ← (( do
                                                            if ((← do
                                                                 (Halted ())) : Bool)
                                                            then
                                                              (do
                                                                let w__91 ← (( do (EDSCR_read ())
                                                                  ) : SailM (BitVec 32) )
                                                                (pure ((((_get_EDSCR_Type_SDD w__91) == 1#1) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__92 : Bool)
                                                          then sailThrow ((Error_Undefined ()))
                                                          else
                                                            (do
                                                              (AArch32_TakeMonitorTrapException ())))
                                                      else
                                                        (do
                                                          let w__93 ← (( do (HaveEL EL3) ) : SailM
                                                            Bool )
                                                          if (w__93 : Bool)
                                                          then
                                                            (do
                                                              let w__94 ← (( do
                                                                (ICC_CTLR_NS_read ()) ) : SailM
                                                                (BitVec 32) )
                                                              (R_set t (__get_ICC_CTLR_NS w__94)))
                                                          else
                                                            (do
                                                              let w__95 ← (( do (ICC_CTLR_read ())
                                                                ) : SailM (BitVec 32) )
                                                              (R_set t (__get_ICC_CTLR w__95))))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__107 ← (( do
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
                                   let w__99 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                   (pure ((((_get_EDSCR_Type_SDD w__99) == 1#1) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) : Bool)
                     then
                       (do
                         let w__103 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                         (pure (((! w__103) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__105 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    let w__106 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    (pure (((((_get_SCR_EL3_Type_IRQ w__105) +++ (_get_SCR_EL3_Type_FIQ w__106)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__107 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__119 ← (( do
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
                                       let w__111 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                       (pure ((((_get_EDSCR_Type_SDD w__111) == 1#1) : Bool))))
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
                        let w__117 ← (( do readReg SCR ) : SailM (BitVec 32) )
                        let w__118 ← (( do readReg SCR ) : SailM (BitVec 32) )
                        (pure (((((_get_SCR_Type_IRQ w__117) +++ (_get_SCR_Type_FIQ w__118)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__119 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__ICC_HSRE_SRE == 0#1) : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__125 ← (( do
                            if ((← do
                                 if ((← do
                                      (HaveEL EL3)) : Bool)
                                 then
                                   (do
                                     let w__121 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                     (pure (((! w__121) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__123 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                let w__124 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                (pure (((((_get_SCR_EL3_Type_IRQ w__123) +++ (_get_SCR_EL3_Type_FIQ
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
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                          else
                            (do
                              let w__134 ← (( do
                                if ((← do
                                     if ((← do
                                          (HaveEL EL3)) : Bool)
                                     then
                                       (do
                                         (ELUsingAArch32 EL3))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__132 ← (( do readReg SCR ) : SailM (BitVec 32) )
                                    let w__133 ← (( do readReg SCR ) : SailM (BitVec 32) )
                                    (pure (((((_get_SCR_Type_IRQ w__132) +++ (_get_SCR_Type_FIQ
                                            w__133)) == 0b11#2) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__134 : Bool)
                              then
                                (do
                                  let w__137 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__136 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__136) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__137 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch32_TakeMonitorTrapException ())))
                              else
                                (do
                                  let w__138 ← (( do (HaveEL EL3) ) : SailM Bool )
                                  if (w__138 : Bool)
                                  then
                                    (do
                                      let w__139 ← (( do (ICC_CTLR_NS_read ()) ) : SailM
                                        (BitVec 32) )
                                      (R_set t (__get_ICC_CTLR_NS w__139)))
                                  else
                                    (do
                                      let w__140 ← (( do (ICC_CTLR_read ()) ) : SailM (BitVec 32)
                                        )
                                      (R_set t (__get_ICC_CTLR w__140)))))))))
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
                          let w__141 ← (( do (ICC_CTLR_S_read ()) ) : SailM (BitVec 32) )
                          (R_set t (__get_ICC_CTLR_S w__141)))
                      else
                        (do
                          let w__142 ← (( do (ICC_CTLR_NS_read ()) ) : SailM (BitVec 32) )
                          (R_set t (__get_ICC_CTLR_NS w__142)))))
              else (pure (())))))


end ArmFull.Functions
