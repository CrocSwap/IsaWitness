import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0042
import ArmFull.Fn.M0054
import ArmFull.Fn.M0059
import ArmFull.Fn.M0062
import ArmFull.Fn.M0063
import ArmFull.Fn.M0081
import ArmFull.Fn.M0082
import ArmFull.Fn.M0100
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0196
import ArmFull.Fn.M0201
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
def DACR_SysRegWrite32_bfabed8f69d486b5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T3 : (BitVec 1) := (_get_HSTR_EL2_Type_T3 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T3 : (BitVec 1) := (_get_HSTR_Type_T3 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TVM : (BitVec 1) := (_get_HCR_EL2_Type_TVM w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TVM : (BitVec 1) := (_get_HCR_Type_TVM w__4)
  let w__5 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__9 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__7 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__7) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T3 == 1#1) : Bool))) ) : SailM Bool )
          if (w__9 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__13 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T3 == 1#1) : Bool))) ) : SailM Bool )
              if (w__13 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__17 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__15 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__15) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TVM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__17 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__21 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TVM == 1#1) : Bool))) ) : SailM Bool )
                      if (w__21 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__23 ← (( do
                            if (((HaveEL EL3) : Bool) : Bool)
                            then
                              (do
                                (ELUsingAArch32 EL3))
                            else (pure false) ) : SailM Bool )
                          if (w__23 : Bool)
                          then
                            (do
                              let w__24 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (DACR_NS_write (Mk_DACR_Type w__24)))
                          else
                            (do
                              let w__25 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (DACR_write (Mk_DACR_Type w__25))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__27 ← (( do
                if (((HaveEL EL3) : Bool) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__27 : Bool)
              then
                (do
                  let w__28 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (DACR_NS_write (Mk_DACR_Type w__28)))
              else
                (do
                  let w__29 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (DACR_write (Mk_DACR_Type w__29))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__31 ← (( do
                    if (((__SCR_NS == 0#1) : Bool) : Bool)
                    then
                      (do
                        let w__30 ← (( do readReg CP15SDISABLE ) : SailM Signal )
                        (pure (((BEq.beq w__30 Signal_High) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__31 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__33 ← (( do
                        if (((__SCR_NS == 0#1) : Bool) : Bool)
                        then
                          (do
                            let w__32 ← (( do readReg CP15SDISABLE2 ) : SailM Signal )
                            (pure (((BEq.beq w__32 Signal_High) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__33 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          if ((__SCR_NS == 0#1) : Bool)
                          then
                            (do
                              let w__34 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              writeReg DACR_S (Mk_DACR_Type w__34))
                          else
                            (do
                              let w__35 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (DACR_NS_write (Mk_DACR_Type w__35))))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DBGBCR_SysRegWrite32_08e08cceb84c7c71 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_TDA : (BitVec 1) := (_get_EDSCR_Type_TDA w__2)
  let w__3 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
  if ((8 ≥b w__3) : Bool)
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
                                  (DBGBCR_set 8 (Mk_DBGBCR_Type w__35))))))))
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
                              (DBGBCR_set 8 (Mk_DBGBCR_Type w__55))))))
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
                          (DBGBCR_set 8 (Mk_DBGBCR_Type w__60))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def DBGBCR_SysRegWrite32_122d009e13ded976 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_TDA : (BitVec 1) := (_get_EDSCR_Type_TDA w__2)
  let w__3 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
  if ((1 ≥b w__3) : Bool)
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
                                  (DBGBCR_set 1 (Mk_DBGBCR_Type w__35))))))))
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
                              (DBGBCR_set 1 (Mk_DBGBCR_Type w__55))))))
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
                          (DBGBCR_set 1 (Mk_DBGBCR_Type w__60))))
                  else (pure (()))))))


end ArmFull.Functions
