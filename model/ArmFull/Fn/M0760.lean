module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0010
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0043
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0054
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0086
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0195
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0212
public import ArmFull.Fn.M0227
public import ArmFull.Fn.M0252
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
def CP15ISB_SysRegWrite32_b2e3d8ab360938e2 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_CP15BEN : (BitVec 1) := (_get_SCTLR_EL1_Type_CP15BEN w__1)
  let w__2 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let __SCTLR_EL2_CP15BEN : (BitVec 1) := (_get_SCTLR_EL2_Type_CP15BEN w__2)
  let w__3 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  let __SCTLR_CP15BEN : (BitVec 1) := (_get_SCTLR_Type_CP15BEN w__3)
  let w__4 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T7 : (BitVec 1) := (_get_HSTR_EL2_Type_T7 w__4)
  let w__5 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T7 : (BitVec 1) := (_get_HSTR_Type_T7 w__5)
  let w__6 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  let __HSCTLR_CP15BEN : (BitVec 1) := (_get_HSCTLR_Type_CP15BEN w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__13 ← (( do
        (pure ((← do
              if ((← do
                   let w__7 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                   (pure (((! w__7) : Bool)))) : Bool)
              then
                (do
                  let w__11 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_E2H w__9) +++ (_get_HCR_EL2_Type_TGE w__10)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  (pure (((! w__11) : Bool))))
              else (pure false)) && ((__SCTLR_EL1_CP15BEN == 0#1) : Bool))) ) : SailM Bool )
      if (w__13 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__20 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            (EL2Enabled ())) : Bool)
                       then
                         (do
                           let w__15 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                           (pure (((! w__15) : Bool))))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_E2H w__17) +++ (_get_HCR_EL2_Type_TGE w__18)) == 0b11#2) : Bool))))
                  else (pure false)) && ((__SCTLR_EL2_CP15BEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__20 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__22 ← (( do
                (pure ((← do
                      (ELUsingAArch32 EL1)) && ((__SCTLR_CP15BEN == 0#1) : Bool))) ) : SailM Bool )
              if (w__22 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__29 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   let w__24 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                   (pure (((! w__24) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__26) +++ (_get_HCR_EL2_Type_TGE
                                      w__27)) != 0b11#2) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
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
                              else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__33 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else (pure ((CP15ISB ()))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__37 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__35 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__35) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
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
                      else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
              if (w__41 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  if ((__SCTLR_CP15BEN == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else (pure ((CP15ISB ()))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HSCTLR_CP15BEN == 0#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else (pure ((CP15ISB ()))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCTLR_CP15BEN == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else (pure ((CP15ISB ()))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CPACR_SysRegWrite32_512a962d4019b387 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TCPAC : (BitVec 1) := (_get_CPTR_EL3_Type_TCPAC w__1)
  let w__2 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T1 : (BitVec 1) := (_get_HSTR_EL2_Type_T1 w__2)
  let w__3 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T1 : (BitVec 1) := (_get_HSTR_Type_T1 w__3)
  let w__4 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_TCPAC : (BitVec 1) := (_get_CPTR_EL2_Type_TCPAC w__4)
  let w__5 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
  let __HCPTR_TCPAC : (BitVec 1) := (_get_HCPTR_Type_TCPAC w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__15 ← (( do
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
                                let w__9 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__9) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__13 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__13) : Bool))))
                  else (pure false)) && ((__CPTR_EL3_TCPAC == 1#1) : Bool))) ) : SailM Bool )
          if (w__15 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__19 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__17 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__17) : Bool))))
                      else (pure false)) && ((__HSTR_EL2_T1 == 1#1) : Bool))) ) : SailM Bool )
              if (w__19 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__23 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HSTR_T1 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__23 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__27 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__25 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__25) : Bool))))
                              else (pure false)) && ((__CPTR_EL2_TCPAC == 1#1) : Bool))) ) : SailM
                        Bool )
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
                                  else (pure false)) && ((__HCPTR_TCPAC == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__31 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__35 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          let w__33 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__33) : Bool))))
                                      else (pure false)) && ((__CPTR_EL3_TCPAC == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__35 : Bool)
                              then
                                (do
                                  let w__38 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__37 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__37) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__38 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  let w__39 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (__set_CPACR (Mk_CPACR_Type w__39)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__49 ← (( do
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
                                    let w__43 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__43) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__47 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__47) : Bool))))
                      else (pure false)) && ((__CPTR_EL3_TCPAC == 1#1) : Bool))) ) : SailM Bool )
              if (w__49 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__53 ← (( do
                    (pure ((← do
                          if ((← do
                               (HaveEL EL3)) : Bool)
                          then
                            (do
                              let w__51 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__51) : Bool))))
                          else (pure false)) && ((__CPTR_EL3_TCPAC == 1#1) : Bool))) ) : SailM Bool
                    )
                  if (w__53 : Bool)
                  then
                    (do
                      let w__56 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__55 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__55) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__56 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                  else
                    (do
                      let w__57 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (__set_CPACR (Mk_CPACR_Type w__57)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__58 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (__set_CPACR (Mk_CPACR_Type w__58)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CPPRCTX_SysRegWrite32_07d924e6f4753edc (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_EnRCTX : (BitVec 1) := (_get_SCTLR_EL1_Type_EnRCTX w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  let __SCTLR_EnRCTX : (BitVec 1) := (_get_SCTLR_Type_EnRCTX w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TGE : (BitVec 1) := (_get_HCR_Type_TGE w__4)
  let w__5 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T7 : (BitVec 1) := (_get_HSTR_EL2_Type_T7 w__5)
  let w__6 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T7 : (BitVec 1) := (_get_HSTR_Type_T7 w__6)
  let w__7 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__7)
  let w__8 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_CPPRCTX : (BitVec 1) := (_get_HFGITR_EL2_Type_CPPRCTX w__8)
  let w__9 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let __SCTLR_EL2_EnRCTX : (BitVec 1) := (_get_SCTLR_EL2_Type_EnRCTX w__9)
  let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__10)
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
              else (pure false)) && ((__SCTLR_EL1_EnRCTX == 0#1) : Bool))) ) : SailM Bool )
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
                  (ELUsingAArch32 EL1)) && ((__SCTLR_EnRCTX == 0#1) : Bool))) ) : SailM Bool )
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
              let w__38 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                (EL2Enabled ())) : Bool)
                           then
                             (do
                               let w__33 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                               (pure (((! w__33) : Bool))))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__35 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__36 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__35) +++ (_get_HCR_EL2_Type_TGE w__36)) != 0b11#2) : Bool))))
                      else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
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
                          else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__42 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__54 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        if ((← do
                                             if ((← do
                                                  (EL2Enabled ())) : Bool)
                                             then
                                               (do
                                                 let w__44 ← (( do (ELUsingAArch32 EL1) ) : SailM
                                                   Bool )
                                                 (pure (((! w__44) : Bool))))
                                             else (pure false)) : Bool)
                                        then
                                          (do
                                            let w__46 ← (( do readReg HCR_EL2 ) : SailM
                                              (BitVec 64) )
                                            let w__47 ← (( do readReg HCR_EL2 ) : SailM
                                              (BitVec 64) )
                                            (pure (((((_get_HCR_EL2_Type_E2H w__46) +++ (_get_HCR_EL2_Type_TGE
                                                    w__47)) != 0b11#2) : Bool))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (IsFeatureImplemented FEAT_FGT))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (pure ((← do
                                        let w__51 ← (( do (HaveEL EL3) ) : SailM Bool )
                                        (pure (((! w__51) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                              else (pure false)) && ((__HFGITR_EL2_CPPRCTX == 1#1) : Bool))) ) :
                        SailM Bool )
                      if (w__54 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__61 ← (( do
                            (pure ((← do
                                  if ((← do
                                       if ((← do
                                            (EL2Enabled ())) : Bool)
                                       then
                                         (do
                                           let w__56 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                           (pure (((! w__56) : Bool))))
                                       else (pure false)) : Bool)
                                  then
                                    (do
                                      let w__58 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                      let w__59 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                      (pure (((((_get_HCR_EL2_Type_E2H w__58) +++ (_get_HCR_EL2_Type_TGE
                                              w__59)) == 0b11#2) : Bool))))
                                  else (pure false)) && ((__SCTLR_EL2_EnRCTX == 0#1) : Bool))) ) :
                            SailM Bool )
                          if (w__61 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__62 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (AArch32_RestrictPrediction w__62 RestrictType_CachePrefetch))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__66 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__64 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__64) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
          if (w__66 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__70 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
              if (w__70 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__74 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__72 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__72) : Bool))))
                          else (pure false)) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
                  if (w__74 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__75 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (AArch32_RestrictPrediction w__75 RestrictType_CachePrefetch)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__76 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AArch32_RestrictPrediction w__76 RestrictType_CachePrefetch))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__77 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AArch32_RestrictPrediction w__77 RestrictType_CachePrefetch))
              else (pure (())))))


end ArmFull.Functions
