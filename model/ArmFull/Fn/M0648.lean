module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0086
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0140
public import ArmFull.Fn.M0141
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0202
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
def DBGDEVID1_SysRegRead32_faeb62347ce88c7a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                          let w__31 ← (( do readReg DBGDEVID1 ) : SailM (BitVec 32) )
                          (R_set t (__get_DBGDEVID1 w__31)))))))
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
                      let w__49 ← (( do readReg DBGDEVID1 ) : SailM (BitVec 32) )
                      (R_set t (__get_DBGDEVID1 w__49)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__50 ← (( do readReg DBGDEVID1 ) : SailM (BitVec 32) )
                  (R_set t (__get_DBGDEVID1 w__50)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DBGDEVID2_SysRegRead32_6baefcc664f89312 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                          let w__31 ← (( do readReg DBGDEVID2 ) : SailM (BitVec 32) )
                          (R_set t (__get_DBGDEVID2 w__31)))))))
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
                      let w__49 ← (( do readReg DBGDEVID2 ) : SailM (BitVec 32) )
                      (R_set t (__get_DBGDEVID2 w__49)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__50 ← (( do readReg DBGDEVID2 ) : SailM (BitVec 32) )
                  (R_set t (__get_DBGDEVID2 w__50)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DBGDEVID_SysRegRead32_66290830e754b76a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                          let w__31 ← (( do readReg DBGDEVID ) : SailM (BitVec 32) )
                          (R_set t w__31))))))
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
                      let w__49 ← (( do readReg DBGDEVID ) : SailM (BitVec 32) )
                      (R_set t w__49))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__50 ← (( do readReg DBGDEVID ) : SailM (BitVec 32) )
                  (R_set t w__50))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DBGDIDR_SysRegRead32_8ee636612218bdd3 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__1)
  let w__2 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  let __MDSCR_EL1_TDCC : (BitVec 1) := (_get_MDSCR_EL1_Type_TDCC w__2)
  let w__3 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
  let __DBGDSCRext_UDCCdis : (BitVec 1) := (_get_DBGDSCRext_Type_UDCCdis w__3)
  let w__6 ← (( do
    if ((← do
         (Halted ())) : Bool)
    then
      (do
        (ConstrainUnpredictableBool Unpredictable_IGNORETRAPINDEBUG))
    else (pure false) ) : SailM Bool )
  if (w__6 : Bool)
  then
    (do
      let w__7 ← (( do readReg DBGDIDR ) : SailM (BitVec 32) )
      (R_set t (__get_DBGDIDR w__7)))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
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
                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
          if (w__17 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__19 ← (( do
                (pure ((← do
                      let w__18 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                      (pure (((! w__18) : Bool)))) && ((__MDSCR_EL1_TDCC == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__19 : Bool)
              then
                (do
                  let w__24 ← (( do
                    if ((← do
                         if ((← do
                              (EL2Enabled ())) : Bool)
                         then
                           (do
                             let w__21 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                             (pure (((! w__21) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__23 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure ((((_get_HCR_EL2_Type_TGE w__23) == 1#1) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__24 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                  else
                    (do
                      (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x05#8))))
              else
                (do
                  let w__26 ← (( do
                    (pure ((← do
                          (ELUsingAArch32 EL1)) && ((__DBGDSCRext_UDCCdis == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__26 : Bool)
                  then
                    (do
                      let w__31 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 let w__28 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                 (pure (((! w__28) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__30 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                            (pure ((((_get_HCR_EL2_Type_TGE w__30) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__31 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          let w__36 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     (ELUsingAArch32 EL2))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__35 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_HCR_Type_TGE w__35) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__36 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                          else sailThrow ((Error_Undefined ()))))
                  else
                    (do
                      let w__44 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 let w__38 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                 (pure (((! w__38) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            if ((← do
                                 let w__40 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 (pure ((((_get_HCR_EL2_Type_TGE w__40) == 1#1) : Bool)))) : Bool)
                            then (pure true)
                            else
                              (do
                                let w__41 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                                let w__42 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                                (pure (((((_get_MDCR_EL2_Type_TDE w__41) +++ (_get_MDCR_EL2_Type_TDA
                                        w__42)) != 0b00#2) : Bool)))))
                        else (pure false) ) : SailM Bool )
                      if (w__44 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          let w__52 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     (ELUsingAArch32 EL2))
                                 else (pure false)) : Bool)
                            then
                              (do
                                if ((← do
                                     let w__48 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                                     (pure ((((_get_HCR_Type_TGE w__48) == 1#1) : Bool)))) : Bool)
                                then (pure true)
                                else
                                  (do
                                    let w__49 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                                    let w__50 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                                    (pure (((((_get_HDCR_Type_TDE w__49) +++ (_get_HDCR_Type_TDA
                                            w__50)) != 0b00#2) : Bool)))))
                            else (pure false) ) : SailM Bool )
                          if (w__52 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                          else
                            (do
                              let w__56 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          let w__54 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__54) : Bool))))
                                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__56 : Bool)
                              then
                                (do
                                  let w__59 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__58 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__58) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__59 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                              else
                                (do
                                  let w__60 ← (( do readReg DBGDIDR ) : SailM (BitVec 32) )
                                  (R_set t (__get_DBGDIDR w__60)))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
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
                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
              if (w__70 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__76 ← (( do
                    if ((← do
                         if ((← do
                              (EL2Enabled ())) : Bool)
                         then
                           (do
                             let w__72 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                             (pure (((! w__72) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__74 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        let w__75 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_MDCR_EL2_Type_TDE w__74) +++ (_get_MDCR_EL2_Type_TDA w__75)) != 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__76 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                  else
                    (do
                      let w__82 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 (ELUsingAArch32 EL2))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__80 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                            let w__81 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                            (pure (((((_get_HDCR_Type_TDE w__80) +++ (_get_HDCR_Type_TDA w__81)) != 0b00#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__82 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                      else
                        (do
                          let w__86 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (HaveEL EL3)) : Bool)
                                  then
                                    (do
                                      let w__84 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__84) : Bool))))
                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__86 : Bool)
                          then
                            (do
                              let w__89 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__88 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__88) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__89 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                          else
                            (do
                              let w__90 ← (( do readReg DBGDIDR ) : SailM (BitVec 32) )
                              (R_set t (__get_DBGDIDR w__90)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__100 ← (( do
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
                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__100 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__104 ← (( do
                        (pure ((← do
                              if ((← do
                                   (HaveEL EL3)) : Bool)
                              then
                                (do
                                  let w__102 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__102) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__104 : Bool)
                      then
                        (do
                          let w__107 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__106 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__106) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__107 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                      else
                        (do
                          let w__108 ← (( do readReg DBGDIDR ) : SailM (BitVec 32) )
                          (R_set t (__get_DBGDIDR w__108)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__109 ← (( do readReg DBGDIDR ) : SailM (BitVec 32) )
                      (R_set t (__get_DBGDIDR w__109)))
                  else (pure (()))))))


end ArmFull.Functions
