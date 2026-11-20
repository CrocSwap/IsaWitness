module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0054
public import ArmFull.Fn.M0055
public import ArmFull.Fn.M0082
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0201
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
def DBGOSECCR_SysRegWrite32_87878830bf235bef (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__1)
  let w__2 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
  let __DBGOSLSR_OSLK : (BitVec 1) := (_get_DBGOSLSR_Type_OSLK w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__12 ← (( do
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
                                let w__6 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__6) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__10 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__10) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
          if (w__12 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__18 ← (( do
                if ((← do
                     if ((← do
                          (EL2Enabled ())) : Bool)
                     then
                       (do
                         let w__14 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                         (pure (((! w__14) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__16 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                    let w__17 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_MDCR_EL2_Type_TDE w__16) +++ (_get_MDCR_EL2_Type_TDA w__17)) != 0b00#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__18 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
              else
                (do
                  let w__24 ← (( do
                    if ((← do
                         if ((← do
                              (EL2Enabled ())) : Bool)
                         then
                           (do
                             (ELUsingAArch32 EL2))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__22 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                        let w__23 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                        (pure (((((_get_HDCR_Type_TDE w__22) +++ (_get_HDCR_Type_TDA w__23)) != 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__24 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                  else
                    (do
                      let w__28 ← (( do
                        (pure ((← do
                              if ((← do
                                   (HaveEL EL3)) : Bool)
                              then
                                (do
                                  let w__26 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__26) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__28 : Bool)
                      then
                        (do
                          let w__31 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__30 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__30) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__31 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                      else
                        (do
                          if ((__DBGOSLSR_OSLK == 0#1) : Bool)
                          then (pure (()))
                          else
                            (do
                              let w__32 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (DBGOSECCR_write (Mk_DBGOSECCR_Type w__32))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__42 ← (( do
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
                                    let w__36 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__36) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__40 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__40) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
              if (w__42 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__46 ← (( do
                    (pure ((← do
                          if ((← do
                               (HaveEL EL3)) : Bool)
                          then
                            (do
                              let w__44 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__44) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__46 : Bool)
                  then
                    (do
                      let w__49 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__48 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__48) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__49 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                  else
                    (do
                      if ((__DBGOSLSR_OSLK == 0#1) : Bool)
                      then (pure (()))
                      else
                        (do
                          let w__50 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (DBGOSECCR_write (Mk_DBGOSECCR_Type w__50))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__DBGOSLSR_OSLK == 0#1) : Bool)
                  then (pure (()))
                  else
                    (do
                      let w__51 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (DBGOSECCR_write (Mk_DBGOSECCR_Type w__51))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DBGOSLAR_SysRegWrite32_38360f8339ba583f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDOSA : (BitVec 1) := (_get_MDCR_EL3_Type_TDOSA w__1)
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
                  else (pure false)) && ((__MDCR_EL3_TDOSA == 1#1) : Bool))) ) : SailM Bool )
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
                    (pure (((((_get_MDCR_EL2_Type_TDE w__15) +++ (_get_MDCR_EL2_Type_TDOSA w__16)) != 0b00#2) : Bool))))
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
                        (pure (((((_get_HDCR_Type_TDE w__21) +++ (_get_HDCR_Type_TDOSA w__22)) != 0b00#2) : Bool))))
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
                              else (pure false)) && ((__MDCR_EL3_TDOSA == 1#1) : Bool))) ) : SailM
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
                          writeReg DBGOSLAR (Mk_DBGOSLAR_Type w__31))))))
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
                      else (pure false)) && ((__MDCR_EL3_TDOSA == 1#1) : Bool))) ) : SailM Bool )
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
                          else (pure false)) && ((__MDCR_EL3_TDOSA == 1#1) : Bool))) ) : SailM Bool
                    )
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
                      writeReg DBGOSLAR (Mk_DBGOSLAR_Type w__49))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__50 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  writeReg DBGOSLAR (Mk_DBGOSLAR_Type w__50))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DBGPRCR_SysRegWrite32_99fa790871277002 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDOSA : (BitVec 1) := (_get_MDCR_EL3_Type_TDOSA w__1)
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
                  else (pure false)) && ((__MDCR_EL3_TDOSA == 1#1) : Bool))) ) : SailM Bool )
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
                    (pure (((((_get_MDCR_EL2_Type_TDE w__15) +++ (_get_MDCR_EL2_Type_TDOSA w__16)) != 0b00#2) : Bool))))
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
                        (pure (((((_get_HDCR_Type_TDE w__21) +++ (_get_HDCR_Type_TDOSA w__22)) != 0b00#2) : Bool))))
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
                              else (pure false)) && ((__MDCR_EL3_TDOSA == 1#1) : Bool))) ) : SailM
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
                          (DBGPRCR_write (Mk_DBGPRCR_Type w__31)))))))
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
                      else (pure false)) && ((__MDCR_EL3_TDOSA == 1#1) : Bool))) ) : SailM Bool )
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
                          else (pure false)) && ((__MDCR_EL3_TDOSA == 1#1) : Bool))) ) : SailM Bool
                    )
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
                      (DBGPRCR_write (Mk_DBGPRCR_Type w__49)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__50 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (DBGPRCR_write (Mk_DBGPRCR_Type w__50)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DBGVCR_SysRegWrite32_fc44294faccd3e66 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                          (DBGVCR_write (Mk_DBGVCR_Type w__31)))))))
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
                      (DBGVCR_write (Mk_DBGVCR_Type w__49)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__50 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (DBGVCR_write (Mk_DBGVCR_Type w__50)))
              else (pure (())))))


end ArmFull.Functions
