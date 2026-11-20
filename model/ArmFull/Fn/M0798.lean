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
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0054
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0083
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
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
def ERXMISC2_SysRegWrite32_3da1683956813628 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_TERR : (BitVec 1) := (_get_SCR_EL3_Type_TERR w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_TWERR : (BitVec 1) := (_get_SCR_EL3_Type_TWERR w__2)
  let w__3 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_TERR : (BitVec 1) := (_get_SCR_Type_TERR w__3)
  let w__4 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T5 : (BitVec 1) := (_get_HSTR_EL2_Type_T5 w__4)
  let w__5 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T5 : (BitVec 1) := (_get_HSTR_Type_T5 w__5)
  let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TERR : (BitVec 1) := (_get_HCR_EL2_Type_TERR w__6)
  let w__7 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
  let __HCR2_TERR : (BitVec 1) := (_get_HCR2_Type_TERR w__7)
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_M : (BitVec 5) := w__8.M
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__18 ← (( do
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
                                let w__12 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__12) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__16 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__16) : Bool))))
                  else (pure false)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM Bool )
          if (w__18 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__28 ← (( do
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
                                    let w__22 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__22) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__26 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__26) : Bool))))
                      else (pure false)) && ((__SCR_EL3_TWERR == 1#1) : Bool))) ) : SailM Bool )
              if (w__28 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__38 ← (( do
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
                                        let w__32 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__32) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL3))
                          else (pure false)) && ((__SCR_TERR == 1#1) : Bool))) ) : SailM Bool )
                  if (w__38 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__42 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__40 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__40) : Bool))))
                              else (pure false)) && ((__HSTR_EL2_T5 == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__42 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__46 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HSTR_T5 == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__46 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__50 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          let w__48 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                          (pure (((! w__48) : Bool))))
                                      else (pure false)) && ((__HCR_EL2_TERR == 1#1) : Bool))) ) :
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
                                          else (pure false)) && ((__HCR2_TERR == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__54 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      let w__58 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (HaveEL EL3)) : Bool)
                                              then
                                                (do
                                                  let w__56 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                    Bool )
                                                  (pure (((! w__56) : Bool))))
                                              else (pure false)) && ((__SCR_EL3_TERR == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__58 : Bool)
                                      then
                                        (do
                                          let w__61 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__60 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__60) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__61 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x03#8))))
                                      else
                                        (do
                                          let w__65 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       (HaveEL EL3)) : Bool)
                                                  then
                                                    (do
                                                      let w__63 ← (( do (ELUsingAArch32 EL3) ) :
                                                        SailM Bool )
                                                      (pure (((! w__63) : Bool))))
                                                  else (pure false)) && ((__SCR_EL3_TWERR == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__65 : Bool)
                                          then
                                            (do
                                              let w__68 ← (( do
                                                if ((← do
                                                     (Halted ())) : Bool)
                                                then
                                                  (do
                                                    let w__67 ← (( do (EDSCR_read ()) ) : SailM
                                                      (BitVec 32) )
                                                    (pure ((((_get_EDSCR_Type_SDD w__67) == 1#1) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__68 : Bool)
                                              then sailThrow ((Error_Undefined ()))
                                              else
                                                (do
                                                  (AArch64_AArch32SystemAccessTrap EL3
                                                    (BitVec.toNat 0x03#8))))
                                          else
                                            (do
                                              let w__73 ← (( do
                                                (pure ((← do
                                                      (pure ((← do
                                                            if ((← do
                                                                 (HaveEL EL3)) : Bool)
                                                            then
                                                              (do
                                                                (ELUsingAArch32 EL3))
                                                            else (pure false)) && ((__PSTATE_M != M32_Monitor) : Bool)))) && ((__SCR_TERR == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__73 : Bool)
                                              then
                                                (do
                                                  let w__76 ← (( do
                                                    if ((← do
                                                         (Halted ())) : Bool)
                                                    then
                                                      (do
                                                        let w__75 ← (( do (EDSCR_read ()) ) :
                                                          SailM (BitVec 32) )
                                                        (pure ((((_get_EDSCR_Type_SDD w__75) == 1#1) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__76 : Bool)
                                                  then sailThrow ((Error_Undefined ()))
                                                  else
                                                    (do
                                                      (AArch32_TakeMonitorTrapException ())))
                                              else
                                                (do
                                                  let w__77 ← (( do (R_read t) ) : SailM
                                                    (BitVec 32) )
                                                  (ERXMISC2_write w__77))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__87 ← (( do
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
                                    let w__81 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__81) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__85 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__85) : Bool))))
                      else (pure false)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM Bool )
              if (w__87 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__97 ← (( do
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
                          else (pure false)) && ((__SCR_EL3_TWERR == 1#1) : Bool))) ) : SailM Bool )
                  if (w__97 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__107 ← (( do
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
                                            let w__101 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__101) == 1#1) : Bool))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL3))
                              else (pure false)) && ((__SCR_TERR == 1#1) : Bool))) ) : SailM Bool )
                      if (w__107 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__111 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (HaveEL EL3)) : Bool)
                                  then
                                    (do
                                      let w__109 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__109) : Bool))))
                                  else (pure false)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__111 : Bool)
                          then
                            (do
                              let w__114 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__113 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__113) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__114 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                          else
                            (do
                              let w__118 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          let w__116 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__116) : Bool))))
                                      else (pure false)) && ((__SCR_EL3_TWERR == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__118 : Bool)
                              then
                                (do
                                  let w__121 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__120 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__120) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__121 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  let w__125 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (HaveEL EL3)) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL3))
                                          else (pure false)) && ((__SCR_TERR == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__125 : Bool)
                                  then
                                    (do
                                      let w__128 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__127 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__127) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__128 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch32_TakeMonitorTrapException ())))
                                  else
                                    (do
                                      let w__129 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      (ERXMISC2_write w__129))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SCR_TERR == 1#1)) : Bool)
                  then
                    (do
                      (AArch32_TakeMonitorTrapException ()))
                  else
                    (do
                      let w__130 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (ERXMISC2_write w__130)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ERXMISC3_SysRegWrite32_427198a3f5bc0b89 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_TERR : (BitVec 1) := (_get_SCR_EL3_Type_TERR w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_TWERR : (BitVec 1) := (_get_SCR_EL3_Type_TWERR w__2)
  let w__3 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_TERR : (BitVec 1) := (_get_SCR_Type_TERR w__3)
  let w__4 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T5 : (BitVec 1) := (_get_HSTR_EL2_Type_T5 w__4)
  let w__5 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T5 : (BitVec 1) := (_get_HSTR_Type_T5 w__5)
  let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TERR : (BitVec 1) := (_get_HCR_EL2_Type_TERR w__6)
  let w__7 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
  let __HCR2_TERR : (BitVec 1) := (_get_HCR2_Type_TERR w__7)
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_M : (BitVec 5) := w__8.M
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__18 ← (( do
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
                                let w__12 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__12) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__16 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__16) : Bool))))
                  else (pure false)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM Bool )
          if (w__18 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__28 ← (( do
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
                                    let w__22 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__22) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__26 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__26) : Bool))))
                      else (pure false)) && ((__SCR_EL3_TWERR == 1#1) : Bool))) ) : SailM Bool )
              if (w__28 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__38 ← (( do
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
                                        let w__32 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__32) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL3))
                          else (pure false)) && ((__SCR_TERR == 1#1) : Bool))) ) : SailM Bool )
                  if (w__38 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__42 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__40 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__40) : Bool))))
                              else (pure false)) && ((__HSTR_EL2_T5 == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__42 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__46 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HSTR_T5 == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__46 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__50 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          let w__48 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                          (pure (((! w__48) : Bool))))
                                      else (pure false)) && ((__HCR_EL2_TERR == 1#1) : Bool))) ) :
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
                                          else (pure false)) && ((__HCR2_TERR == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__54 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                                  else
                                    (do
                                      let w__58 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (HaveEL EL3)) : Bool)
                                              then
                                                (do
                                                  let w__56 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                    Bool )
                                                  (pure (((! w__56) : Bool))))
                                              else (pure false)) && ((__SCR_EL3_TERR == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__58 : Bool)
                                      then
                                        (do
                                          let w__61 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__60 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__60) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__61 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x03#8))))
                                      else
                                        (do
                                          let w__65 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       (HaveEL EL3)) : Bool)
                                                  then
                                                    (do
                                                      let w__63 ← (( do (ELUsingAArch32 EL3) ) :
                                                        SailM Bool )
                                                      (pure (((! w__63) : Bool))))
                                                  else (pure false)) && ((__SCR_EL3_TWERR == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__65 : Bool)
                                          then
                                            (do
                                              let w__68 ← (( do
                                                if ((← do
                                                     (Halted ())) : Bool)
                                                then
                                                  (do
                                                    let w__67 ← (( do (EDSCR_read ()) ) : SailM
                                                      (BitVec 32) )
                                                    (pure ((((_get_EDSCR_Type_SDD w__67) == 1#1) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__68 : Bool)
                                              then sailThrow ((Error_Undefined ()))
                                              else
                                                (do
                                                  (AArch64_AArch32SystemAccessTrap EL3
                                                    (BitVec.toNat 0x03#8))))
                                          else
                                            (do
                                              let w__73 ← (( do
                                                (pure ((← do
                                                      (pure ((← do
                                                            if ((← do
                                                                 (HaveEL EL3)) : Bool)
                                                            then
                                                              (do
                                                                (ELUsingAArch32 EL3))
                                                            else (pure false)) && ((__PSTATE_M != M32_Monitor) : Bool)))) && ((__SCR_TERR == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__73 : Bool)
                                              then
                                                (do
                                                  let w__76 ← (( do
                                                    if ((← do
                                                         (Halted ())) : Bool)
                                                    then
                                                      (do
                                                        let w__75 ← (( do (EDSCR_read ()) ) :
                                                          SailM (BitVec 32) )
                                                        (pure ((((_get_EDSCR_Type_SDD w__75) == 1#1) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__76 : Bool)
                                                  then sailThrow ((Error_Undefined ()))
                                                  else
                                                    (do
                                                      (AArch32_TakeMonitorTrapException ())))
                                              else
                                                (do
                                                  let w__77 ← (( do (R_read t) ) : SailM
                                                    (BitVec 32) )
                                                  (ERXMISC3_write w__77))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__87 ← (( do
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
                                    let w__81 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__81) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__85 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__85) : Bool))))
                      else (pure false)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM Bool )
              if (w__87 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__97 ← (( do
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
                          else (pure false)) && ((__SCR_EL3_TWERR == 1#1) : Bool))) ) : SailM Bool )
                  if (w__97 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__107 ← (( do
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
                                            let w__101 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__101) == 1#1) : Bool))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL3))
                              else (pure false)) && ((__SCR_TERR == 1#1) : Bool))) ) : SailM Bool )
                      if (w__107 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__111 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (HaveEL EL3)) : Bool)
                                  then
                                    (do
                                      let w__109 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__109) : Bool))))
                                  else (pure false)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__111 : Bool)
                          then
                            (do
                              let w__114 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__113 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__113) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__114 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                          else
                            (do
                              let w__118 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          let w__116 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__116) : Bool))))
                                      else (pure false)) && ((__SCR_EL3_TWERR == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__118 : Bool)
                              then
                                (do
                                  let w__121 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__120 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__120) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__121 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                              else
                                (do
                                  let w__125 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (HaveEL EL3)) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL3))
                                          else (pure false)) && ((__SCR_TERR == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__125 : Bool)
                                  then
                                    (do
                                      let w__128 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__127 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__127) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__128 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch32_TakeMonitorTrapException ())))
                                  else
                                    (do
                                      let w__129 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                      (ERXMISC3_write w__129))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SCR_TERR == 1#1)) : Bool)
                  then
                    (do
                      (AArch32_TakeMonitorTrapException ()))
                  else
                    (do
                      let w__130 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (ERXMISC3_write w__130)))
              else (pure (())))))


end ArmFull.Functions
