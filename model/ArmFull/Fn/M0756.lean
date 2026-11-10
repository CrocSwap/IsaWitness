import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0021
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0053
import ArmFull.Fn.M0055
import ArmFull.Fn.M0063
import ArmFull.Fn.M0081
import ArmFull.Fn.M0100
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0196
import ArmFull.Fn.M0202
import ArmFull.Fn.M0246
import ArmFull.Fn.M0254
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
          let w__10 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                            then
                              (do
                                let w__4 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__4) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__8 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__8) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TDOSA == 1#1) : Bool))) ) : SailM Bool )
          if (w__10 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__16 ← (( do
                if ((← do
                     if ((← do
                          (EL2Enabled ())) : Bool)
                     then
                       (do
                         let w__12 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                         (pure (((! w__12) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__14 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                    let w__15 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_MDCR_EL2_Type_TDE w__14) +++ (_get_MDCR_EL2_Type_TDOSA w__15)) != 0b00#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__16 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
              else
                (do
                  let w__22 ← (( do
                    if ((← do
                         if ((← do
                              (EL2Enabled ())) : Bool)
                         then
                           (do
                             (ELUsingAArch32 EL2))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__20 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                        let w__21 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                        (pure (((((_get_HDCR_Type_TDE w__20) +++ (_get_HDCR_Type_TDOSA w__21)) != 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__22 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                  else
                    (do
                      let w__25 ← (( do
                        (pure ((← do
                              if (((HaveEL EL3) : Bool) : Bool)
                              then
                                (do
                                  let w__23 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__23) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TDOSA == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__25 : Bool)
                      then
                        (do
                          let w__28 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__27 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__27) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__28 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                      else
                        (do
                          let w__29 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (DBGPRCR_write (Mk_DBGPRCR_Type w__29)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__38 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
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
                          let w__36 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__36) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TDOSA == 1#1) : Bool))) ) : SailM Bool )
              if (w__38 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__41 ← (( do
                    (pure ((← do
                          if (((HaveEL EL3) : Bool) : Bool)
                          then
                            (do
                              let w__39 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__39) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TDOSA == 1#1) : Bool))) ) : SailM Bool
                    )
                  if (w__41 : Bool)
                  then
                    (do
                      let w__44 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__43 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__43) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__44 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                  else
                    (do
                      let w__45 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (DBGPRCR_write (Mk_DBGPRCR_Type w__45)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__46 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (DBGPRCR_write (Mk_DBGPRCR_Type w__46)))
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
          let w__10 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                            then
                              (do
                                let w__4 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__4) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__8 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__8) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
          if (w__10 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__16 ← (( do
                if ((← do
                     if ((← do
                          (EL2Enabled ())) : Bool)
                     then
                       (do
                         let w__12 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                         (pure (((! w__12) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__14 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                    let w__15 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_MDCR_EL2_Type_TDE w__14) +++ (_get_MDCR_EL2_Type_TDA w__15)) != 0b00#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__16 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
              else
                (do
                  let w__22 ← (( do
                    if ((← do
                         if ((← do
                              (EL2Enabled ())) : Bool)
                         then
                           (do
                             (ELUsingAArch32 EL2))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__20 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                        let w__21 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                        (pure (((((_get_HDCR_Type_TDE w__20) +++ (_get_HDCR_Type_TDA w__21)) != 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__22 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                  else
                    (do
                      let w__25 ← (( do
                        (pure ((← do
                              if (((HaveEL EL3) : Bool) : Bool)
                              then
                                (do
                                  let w__23 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__23) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__25 : Bool)
                      then
                        (do
                          let w__28 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__27 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__27) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__28 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                      else
                        (do
                          let w__29 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (DBGVCR_write (Mk_DBGVCR_Type w__29)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__38 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
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
                          let w__36 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__36) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
              if (w__38 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__41 ← (( do
                    (pure ((← do
                          if (((HaveEL EL3) : Bool) : Bool)
                          then
                            (do
                              let w__39 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__39) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__41 : Bool)
                  then
                    (do
                      let w__44 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__43 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__43) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__44 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                  else
                    (do
                      let w__45 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (DBGVCR_write (Mk_DBGVCR_Type w__45)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__46 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (DBGVCR_write (Mk_DBGVCR_Type w__46)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DBGWCR_SysRegWrite32_0d78661888bb9fac (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_TDA : (BitVec 1) := (_get_EDSCR_Type_TDA w__2)
  let w__3 ← (( do readReg NUM_WATCHPOINTS ) : SailM Int )
  if ((15 ≥b w__3) : Bool)
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
              let w__12 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
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
                          let w__27 ← (( do
                            (pure ((← do
                                  if (((HaveEL EL3) : Bool) : Bool)
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
                              let w__34 ← (( do
                                (pure ((← do
                                      if ((← do
                                           let w__31 ← (( do (DBGOSLSR_read ()) ) : SailM
                                             (BitVec 32) )
                                           (pure ((((_get_DBGOSLSR_Type_OSLK w__31) == 0#1) : Bool)))) : Bool)
                                      then
                                        (do
                                          (HaltingAllowed ()))
                                      else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__34 : Bool)
                              then
                                (do
                                  (Halt DebugHalt_SoftwareAccess))
                              else
                                (do
                                  let w__35 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (DBGWCR_set 15 (Mk_DBGWCR_Type w__35))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__44 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         (pure ((← do
                                               (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                    then
                                      (do
                                        let w__38 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__38) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__42 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__42) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__44 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__47 ← (( do
                        (pure ((← do
                              if (((HaveEL EL3) : Bool) : Bool)
                              then
                                (do
                                  let w__45 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__45) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__47 : Bool)
                      then
                        (do
                          let w__50 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__49 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__49) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__50 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                      else
                        (do
                          let w__54 ← (( do
                            (pure ((← do
                                  if ((← do
                                       let w__51 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32)
                                         )
                                       (pure ((((_get_DBGOSLSR_Type_OSLK w__51) == 0#1) : Bool)))) : Bool)
                                  then
                                    (do
                                      (HaltingAllowed ()))
                                  else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__54 : Bool)
                          then
                            (do
                              (Halt DebugHalt_SoftwareAccess))
                          else
                            (do
                              let w__55 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (DBGWCR_set 15 (Mk_DBGWCR_Type w__55))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__59 ← (( do
                        (pure ((← do
                              if ((← do
                                   let w__56 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
                                   (pure ((((_get_DBGOSLSR_Type_OSLK w__56) == 0#1) : Bool)))) : Bool)
                              then
                                (do
                                  (HaltingAllowed ()))
                              else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__59 : Bool)
                      then
                        (do
                          (Halt DebugHalt_SoftwareAccess))
                      else
                        (do
                          let w__60 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (DBGWCR_set 15 (Mk_DBGWCR_Type w__60))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def DBGWCR_SysRegWrite32_16fb8a88dc2a6a09 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_TDA : (BitVec 1) := (_get_EDSCR_Type_TDA w__2)
  let w__3 ← (( do readReg NUM_WATCHPOINTS ) : SailM Int )
  if ((14 ≥b w__3) : Bool)
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
              let w__12 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
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
                          let w__27 ← (( do
                            (pure ((← do
                                  if (((HaveEL EL3) : Bool) : Bool)
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
                              let w__34 ← (( do
                                (pure ((← do
                                      if ((← do
                                           let w__31 ← (( do (DBGOSLSR_read ()) ) : SailM
                                             (BitVec 32) )
                                           (pure ((((_get_DBGOSLSR_Type_OSLK w__31) == 0#1) : Bool)))) : Bool)
                                      then
                                        (do
                                          (HaltingAllowed ()))
                                      else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__34 : Bool)
                              then
                                (do
                                  (Halt DebugHalt_SoftwareAccess))
                              else
                                (do
                                  let w__35 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (DBGWCR_set 14 (Mk_DBGWCR_Type w__35))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__44 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         (pure ((← do
                                               (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                    then
                                      (do
                                        let w__38 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__38) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__42 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__42) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__44 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__47 ← (( do
                        (pure ((← do
                              if (((HaveEL EL3) : Bool) : Bool)
                              then
                                (do
                                  let w__45 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__45) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__47 : Bool)
                      then
                        (do
                          let w__50 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__49 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__49) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__50 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                      else
                        (do
                          let w__54 ← (( do
                            (pure ((← do
                                  if ((← do
                                       let w__51 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32)
                                         )
                                       (pure ((((_get_DBGOSLSR_Type_OSLK w__51) == 0#1) : Bool)))) : Bool)
                                  then
                                    (do
                                      (HaltingAllowed ()))
                                  else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__54 : Bool)
                          then
                            (do
                              (Halt DebugHalt_SoftwareAccess))
                          else
                            (do
                              let w__55 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (DBGWCR_set 14 (Mk_DBGWCR_Type w__55))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__59 ← (( do
                        (pure ((← do
                              if ((← do
                                   let w__56 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
                                   (pure ((((_get_DBGOSLSR_Type_OSLK w__56) == 0#1) : Bool)))) : Bool)
                              then
                                (do
                                  (HaltingAllowed ()))
                              else (pure false)) && ((__EDSCR_TDA == 1#1) : Bool))) ) : SailM Bool )
                      if (w__59 : Bool)
                      then
                        (do
                          (Halt DebugHalt_SoftwareAccess))
                      else
                        (do
                          let w__60 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (DBGWCR_set 14 (Mk_DBGWCR_Type w__60))))
                  else (pure (()))))))


end ArmFull.Functions
