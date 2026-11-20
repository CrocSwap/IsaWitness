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
public import ArmFull.Fn.M0054
public import ArmFull.Fn.M0056
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0073
public import ArmFull.Fn.M0081
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0200
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
def TPIDRURO_SysRegWrite32_2b144f3027758b96 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__2)
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
                  else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__11 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
              if (w__11 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
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
                      let w__15 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (TPIDRURO_NS_write w__15))
                  else
                    (do
                      let w__16 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (TPIDRURO_write w__16)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__19 ← (( do
                if ((← do
                     (HaveEL EL3)) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__19 : Bool)
              then
                (do
                  let w__20 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (TPIDRURO_NS_write w__20))
              else
                (do
                  let w__21 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (TPIDRURO_write w__21)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then
                    (do
                      let w__22 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      writeReg TPIDRURO_S w__22)
                  else
                    (do
                      let w__23 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (TPIDRURO_NS_write w__23)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TPIDRURW_SysRegWrite32_cb192fad8255358c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR_EL2_TPIDR_EL0 : (BitVec 1) := (_get_HFGWTR_EL2_Type_TPIDR_EL0 w__4)
  let w__5 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__12 ← (( do
        (pure ((← do
              if ((← do
                   if ((← do
                        (EL2Enabled ())) : Bool)
                   then
                     (do
                       let w__7 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                       (pure (((! w__7) : Bool))))
                   else (pure false)) : Bool)
              then
                (do
                  let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure (((((_get_HCR_EL2_Type_E2H w__9) +++ (_get_HCR_EL2_Type_TGE w__10)) != 0b11#2) : Bool))))
              else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
      if (w__12 : Bool)
      then
        (do
          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
      else
        (do
          let w__16 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      (ELUsingAArch32 EL2))
                  else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
          if (w__16 : Bool)
          then
            (do
              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
          else
            (do
              let w__28 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     if ((← do
                                          (EL2Enabled ())) : Bool)
                                     then
                                       (do
                                         let w__18 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                                         (pure (((! w__18) : Bool))))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__20 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__21 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_E2H w__20) +++ (_get_HCR_EL2_Type_TGE
                                            w__21)) != 0b11#2) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (IsFeatureImplemented FEAT_FGT))
                           else (pure false)) : Bool)
                      then
                        (do
                          (pure ((← do
                                let w__25 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__25) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGWTR_EL2_TPIDR_EL0 == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__28 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__29 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (TPIDRURW_write w__29)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
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
                  else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
          if (w__33 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__37 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
              if (w__37 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__40 ← (( do
                    if ((← do
                         (HaveEL EL3)) : Bool)
                    then
                      (do
                        (ELUsingAArch32 EL3))
                    else (pure false) ) : SailM Bool )
                  if (w__40 : Bool)
                  then
                    (do
                      let w__41 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (TPIDRURW_NS_write w__41))
                  else
                    (do
                      let w__42 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (TPIDRURW_write w__42)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__45 ← (( do
                if ((← do
                     (HaveEL EL3)) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__45 : Bool)
              then
                (do
                  let w__46 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (TPIDRURW_NS_write w__46))
              else
                (do
                  let w__47 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (TPIDRURW_write w__47)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then
                    (do
                      let w__48 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      writeReg TPIDRURW_S w__48)
                  else
                    (do
                      let w__49 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (TPIDRURW_NS_write w__49)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TRFCR_SysRegWrite32_e7012a38712cc44a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TTRF : (BitVec 1) := (_get_MDCR_EL3_Type_TTRF w__1)
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_M : (BitVec 5) := w__2.M
  let w__3 ← (( do readReg SDCR ) : SailM (BitVec 32) )
  let __SDCR_TTRF : (BitVec 1) := (_get_SDCR_Type_TTRF w__3)
  let w__4 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T1 : (BitVec 1) := (_get_HSTR_EL2_Type_T1 w__4)
  let w__5 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T1 : (BitVec 1) := (_get_HSTR_Type_T1 w__5)
  let w__6 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TTRF : (BitVec 1) := (_get_MDCR_EL2_Type_TTRF w__6)
  let w__7 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  let __HDCR_TTRF : (BitVec 1) := (_get_HDCR_Type_TTRF w__7)
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
                  else (pure false)) && ((__MDCR_EL3_TTRF == 1#1) : Bool))) ) : SailM Bool )
          if (w__17 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__28 ← (( do
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
                                          let w__21 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32)
                                            )
                                          (pure ((((_get_EDSCR_Type_SDD w__21) == 1#1) : Bool))))
                                      else (pure false)) : Bool)
                                 then
                                   (do
                                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                                 else (pure false)) : Bool)
                            then
                              (do
                                (ELUsingAArch32 EL3))
                            else (pure false)) && ((__PSTATE_M != M32_Monitor) : Bool)))) && ((__SDCR_TTRF == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__28 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__32 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__30 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__30) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T1 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__32 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__36 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HSTR_T1 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__36 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
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
                                  else (pure false)) && ((__MDCR_EL2_TTRF == 1#1) : Bool))) ) :
                            SailM Bool )
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
                                      else (pure false)) && ((__HDCR_TTRF == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__44 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__48 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (HaveEL EL3)) : Bool)
                                          then
                                            (do
                                              let w__46 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                Bool )
                                              (pure (((! w__46) : Bool))))
                                          else (pure false)) && ((__MDCR_EL3_TTRF == 1#1) : Bool)))
                                    ) : SailM Bool )
                                  if (w__48 : Bool)
                                  then
                                    (do
                                      let w__51 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__50 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__50) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__51 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                                  else
                                    (do
                                      let w__56 ← (( do
                                        (pure ((← do
                                              (pure ((← do
                                                    if ((← do
                                                         (HaveEL EL3)) : Bool)
                                                    then
                                                      (do
                                                        (ELUsingAArch32 EL3))
                                                    else (pure false)) && ((__PSTATE_M != M32_Monitor) : Bool)))) && ((__SDCR_TTRF == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__56 : Bool)
                                      then
                                        (do
                                          let w__59 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__58 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__58) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__59 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch32_TakeMonitorTrapException ())))
                                      else
                                        (do
                                          let w__60 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                          (TRFCR_write (Mk_TRFCR_Type w__60)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__70 ← (( do
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
                                    let w__64 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__64) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__68 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__68) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TTRF == 1#1) : Bool))) ) : SailM Bool )
              if (w__70 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__80 ← (( do
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
                                        let w__74 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__74) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL3))
                          else (pure false)) && ((__SDCR_TTRF == 1#1) : Bool))) ) : SailM Bool )
                  if (w__80 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__84 ← (( do
                        (pure ((← do
                              if ((← do
                                   (HaveEL EL3)) : Bool)
                              then
                                (do
                                  let w__82 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__82) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TTRF == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__84 : Bool)
                      then
                        (do
                          let w__87 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__86 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__86) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__87 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          let w__91 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (HaveEL EL3)) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL3))
                                  else (pure false)) && ((__SDCR_TTRF == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__91 : Bool)
                          then
                            (do
                              let w__94 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__93 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__93) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__94 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch32_TakeMonitorTrapException ())))
                          else
                            (do
                              let w__95 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (TRFCR_write (Mk_TRFCR_Type w__95)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SDCR_TTRF == 1#1)) : Bool)
                  then
                    (do
                      (AArch32_TakeMonitorTrapException ()))
                  else
                    (do
                      let w__96 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (TRFCR_write (Mk_TRFCR_Type w__96))))
              else (pure (())))))


end ArmFull.Functions
