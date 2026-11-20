module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0063
public import ArmFull.Fn.M0081
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0195
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0244
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
def DBGWCR_SysRegWrite32_ff5d8b7776f3598d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_TDA : (BitVec 1) := (_get_EDSCR_Type_TDA w__2)
  let w__3 ← (( do readReg NUM_WATCHPOINTS ) : SailM Int )
  if ((10 ≥b w__3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__13 ← (( do
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
                                    let w__7 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__7) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__11 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__11) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
              if (w__13 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__19 ← (( do
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
                        let w__17 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        let w__18 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_MDCR_EL2_Type_TDE w__17) +++ (_get_MDCR_EL2_Type_TDA w__18)) != 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__19 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                  else
                    (do
                      let w__25 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 (ELUsingAArch32 EL2))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__23 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                            let w__24 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                            (pure (((((_get_HDCR_Type_TDE w__23) +++ (_get_HDCR_Type_TDA w__24)) != 0b00#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__25 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                      else
                        (do
                          let w__29 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (HaveEL EL3)) : Bool)
                                  then
                                    (do
                                      let w__27 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__27) : Bool))))
                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__29 : Bool)
                          then
                            (do
                              let w__32 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__31 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__31) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__32 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                          else
                            (do
                              let w__36 ← (( do
                                (pure ((← do
                                      if ((← do
                                           let w__33 ← (( do (DBGOSLSR_read ()) ) : SailM
                                             (BitVec 32) )
                                           (pure ((((_get_DBGOSLSR_Type_OSLK w__33) == 0#1) : Bool)))) : Bool)
                                      then
                                        (do
                                          (HaltingAllowed ()))
                                      else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__36 : Bool)
                              then
                                (do
                                  (Halt DebugHalt_SoftwareAccess))
                              else
                                (do
                                  let w__37 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (DBGWCR_set 10 (Mk_DBGWCR_Type w__37))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__47 ← (( do
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
                                        let w__41 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__41) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__45 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__45) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__47 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__51 ← (( do
                        (pure ((← do
                              if ((← do
                                   (HaveEL EL3)) : Bool)
                              then
                                (do
                                  let w__49 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__49) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__51 : Bool)
                      then
                        (do
                          let w__54 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__53 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__53) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__54 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                      else
                        (do
                          let w__58 ← (( do
                            (pure ((← do
                                  if ((← do
                                       let w__55 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32)
                                         )
                                       (pure ((((_get_DBGOSLSR_Type_OSLK w__55) == 0#1) : Bool)))) : Bool)
                                  then
                                    (do
                                      (HaltingAllowed ()))
                                  else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__58 : Bool)
                          then
                            (do
                              (Halt DebugHalt_SoftwareAccess))
                          else
                            (do
                              let w__59 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (DBGWCR_set 10 (Mk_DBGWCR_Type w__59))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__63 ← (( do
                        (pure ((← do
                              if ((← do
                                   let w__60 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
                                   (pure ((((_get_DBGOSLSR_Type_OSLK w__60) == 0#1) : Bool)))) : Bool)
                              then
                                (do
                                  (HaltingAllowed ()))
                              else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__63 : Bool)
                      then
                        (do
                          (Halt DebugHalt_SoftwareAccess))
                      else
                        (do
                          let w__64 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (DBGWCR_set 10 (Mk_DBGWCR_Type w__64))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def DBGWFAR_SysRegWrite32_a92f4990bd564fb8 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__11 ← (( do
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
                                let w__5 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__5) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__9 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__9) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
          if (w__11 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__17 ← (( do
                if ((← do
                     if ((← do
                          (EL2Enabled ())) : Bool)
                     then
                       (do
                         let w__13 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                         (pure (((! w__13) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__15 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                    let w__16 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_MDCR_EL2_Type_TDE w__15) +++ (_get_MDCR_EL2_Type_TDA w__16)) != 0b00#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__17 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
              else
                (do
                  let w__23 ← (( do
                    if ((← do
                         if ((← do
                              (EL2Enabled ())) : Bool)
                         then
                           (do
                             (ELUsingAArch32 EL2))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__21 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                        let w__22 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                        (pure (((((_get_HDCR_Type_TDE w__21) +++ (_get_HDCR_Type_TDA w__22)) != 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__23 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                  else
                    (do
                      let w__27 ← (( do
                        (pure ((← do
                              if ((← do
                                   (HaveEL EL3)) : Bool)
                              then
                                (do
                                  let w__25 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__25) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__27 : Bool)
                      then
                        (do
                          let w__30 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__29 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__29) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__30 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                      else
                        (do
                          let w__31 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          writeReg DBGWFAR w__31)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__41 ← (( do
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
                                    let w__35 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__35) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__39 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__39) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
              if (w__41 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__45 ← (( do
                    (pure ((← do
                          if ((← do
                               (HaveEL EL3)) : Bool)
                          then
                            (do
                              let w__43 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__43) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__45 : Bool)
                  then
                    (do
                      let w__48 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__47 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__47) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__48 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                  else
                    (do
                      let w__49 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      writeReg DBGWFAR w__49)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__50 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  writeReg DBGWFAR w__50)
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DBGWVR_SysRegWrite32_02f0bae942bffd2c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_TDA : (BitVec 1) := (_get_EDSCR_Type_TDA w__2)
  let w__3 ← (( do readReg NUM_WATCHPOINTS ) : SailM Int )
  if ((3 ≥b w__3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__13 ← (( do
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
                                    let w__7 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__7) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__11 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__11) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
              if (w__13 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__19 ← (( do
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
                        let w__17 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        let w__18 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_MDCR_EL2_Type_TDE w__17) +++ (_get_MDCR_EL2_Type_TDA w__18)) != 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__19 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                  else
                    (do
                      let w__25 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 (ELUsingAArch32 EL2))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__23 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                            let w__24 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                            (pure (((((_get_HDCR_Type_TDE w__23) +++ (_get_HDCR_Type_TDA w__24)) != 0b00#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__25 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                      else
                        (do
                          let w__29 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (HaveEL EL3)) : Bool)
                                  then
                                    (do
                                      let w__27 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__27) : Bool))))
                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__29 : Bool)
                          then
                            (do
                              let w__32 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__31 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__31) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__32 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                          else
                            (do
                              let w__36 ← (( do
                                (pure ((← do
                                      if ((← do
                                           let w__33 ← (( do (DBGOSLSR_read ()) ) : SailM
                                             (BitVec 32) )
                                           (pure ((((_get_DBGOSLSR_Type_OSLK w__33) == 0#1) : Bool)))) : Bool)
                                      then
                                        (do
                                          (HaltingAllowed ()))
                                      else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__36 : Bool)
                              then
                                (do
                                  (Halt DebugHalt_SoftwareAccess))
                              else
                                (do
                                  let w__37 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (DBGWVR_set 3 (Mk_DBGWVR_Type w__37))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__47 ← (( do
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
                                        let w__41 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__41) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__45 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__45) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__47 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__51 ← (( do
                        (pure ((← do
                              if ((← do
                                   (HaveEL EL3)) : Bool)
                              then
                                (do
                                  let w__49 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__49) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__51 : Bool)
                      then
                        (do
                          let w__54 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__53 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__53) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__54 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                      else
                        (do
                          let w__58 ← (( do
                            (pure ((← do
                                  if ((← do
                                       let w__55 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32)
                                         )
                                       (pure ((((_get_DBGOSLSR_Type_OSLK w__55) == 0#1) : Bool)))) : Bool)
                                  then
                                    (do
                                      (HaltingAllowed ()))
                                  else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__58 : Bool)
                          then
                            (do
                              (Halt DebugHalt_SoftwareAccess))
                          else
                            (do
                              let w__59 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (DBGWVR_set 3 (Mk_DBGWVR_Type w__59))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__63 ← (( do
                        (pure ((← do
                              if ((← do
                                   let w__60 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
                                   (pure ((((_get_DBGOSLSR_Type_OSLK w__60) == 0#1) : Bool)))) : Bool)
                              then
                                (do
                                  (HaltingAllowed ()))
                              else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__63 : Bool)
                      then
                        (do
                          (Halt DebugHalt_SoftwareAccess))
                      else
                        (do
                          let w__64 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (DBGWVR_set 3 (Mk_DBGWVR_Type w__64))))
                  else (pure (()))))))


end ArmFull.Functions
