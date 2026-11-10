import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0041
import ArmFull.Fn.M0081
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0151
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0203
import ArmFull.Fn.M0254
import ArmFull.Fn.M0255
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
def DBGDTRTXext_SysRegRead32_dbe218a3250d179f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDCC : (BitVec 1) := (_get_MDCR_EL3_Type_TDCC w__1)
  let w__2 ← (( do readReg SDCR ) : SailM (BitVec 32) )
  let __SDCR_TDCC : (BitVec 1) := (_get_SDCR_Type_TDCC w__2)
  let w__3 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__3)
  let w__4 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TDCC : (BitVec 1) := (_get_MDCR_EL2_Type_TDCC w__4)
  let w__5 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  let __HDCR_TDCC : (BitVec 1) := (_get_HDCR_Type_TDCC w__5)
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_M : (BitVec 5) := w__6.M
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__9 ← (( do
        if ((← do
             (Halted ())) : Bool)
        then
          (do
            (ConstrainUnpredictableBool Unpredictable_IGNORETRAPINDEBUG))
        else (pure false) ) : SailM Bool )
      if (w__9 : Bool)
      then
        (do
          let w__10 ← (( do (DBGDTRTXext_read ()) ) : SailM (BitVec 32) )
          (R_set t w__10))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__19 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                then
                                  (do
                                    let w__13 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__13) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__17 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__17) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
              if (w__19 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__28 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         (pure ((← do
                                               (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
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
                              (ELUsingAArch32 EL3))
                          else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__28 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__37 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        if ((← do
                                             (pure ((← do
                                                   (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                        then
                                          (do
                                            let w__31 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__31) == 1#1) : Bool))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  let w__35 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__35) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                        Bool )
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
                                  else (pure false)) && ((__MDCR_EL2_TDCC == 1#1) : Bool))) ) :
                            SailM Bool )
                          if (w__41 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              let w__45 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HDCR_TDCC == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__45 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                              else
                                (do
                                  let w__51 ← (( do
                                    if ((← do
                                         if ((← do
                                              (EL2Enabled ())) : Bool)
                                         then
                                           (do
                                             let w__47 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool
                                               )
                                             (pure (((! w__47) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__49 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                                        let w__50 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                                        (pure (((((_get_MDCR_EL2_Type_TDE w__49) +++ (_get_MDCR_EL2_Type_TDA
                                                w__50)) != 0b00#2) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__51 : Bool)
                                  then
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                                  else
                                    (do
                                      let w__57 ← (( do
                                        if ((← do
                                             if ((← do
                                                  (EL2Enabled ())) : Bool)
                                             then
                                               (do
                                                 (ELUsingAArch32 EL2))
                                             else (pure false)) : Bool)
                                        then
                                          (do
                                            let w__55 ← (( do (HDCR_read ()) ) : SailM (BitVec 32)
                                              )
                                            let w__56 ← (( do (HDCR_read ()) ) : SailM (BitVec 32)
                                              )
                                            (pure (((((_get_HDCR_Type_TDE w__55) +++ (_get_HDCR_Type_TDA
                                                    w__56)) != 0b00#2) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__57 : Bool)
                                      then
                                        (do
                                          (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                                      else
                                        (do
                                          let w__60 ← (( do
                                            (pure ((← do
                                                  if (((HaveEL EL3) : Bool) : Bool)
                                                  then
                                                    (do
                                                      let w__58 ← (( do (ELUsingAArch32 EL3) ) :
                                                        SailM Bool )
                                                      (pure (((! w__58) : Bool))))
                                                  else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__60 : Bool)
                                          then
                                            (do
                                              let w__63 ← (( do
                                                if ((← do
                                                     (Halted ())) : Bool)
                                                then
                                                  (do
                                                    let w__62 ← (( do (EDSCR_read ()) ) : SailM
                                                      (BitVec 32) )
                                                    (pure ((((_get_EDSCR_Type_SDD w__62) == 1#1) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__63 : Bool)
                                              then sailThrow ((Error_Undefined ()))
                                              else
                                                (do
                                                  (AArch64_AArch32SystemAccessTrap EL3
                                                    (BitVec.toNat 0x05#8))))
                                          else
                                            (do
                                              let w__66 ← (( do
                                                (pure ((← do
                                                      if (((HaveEL EL3) : Bool) : Bool)
                                                      then
                                                        (do
                                                          (ELUsingAArch32 EL3))
                                                      else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__66 : Bool)
                                              then
                                                (do
                                                  let w__69 ← (( do
                                                    if ((← do
                                                         (Halted ())) : Bool)
                                                    then
                                                      (do
                                                        let w__68 ← (( do (EDSCR_read ()) ) :
                                                          SailM (BitVec 32) )
                                                        (pure ((((_get_EDSCR_Type_SDD w__68) == 1#1) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__69 : Bool)
                                                  then sailThrow ((Error_Undefined ()))
                                                  else
                                                    (do
                                                      (AArch32_TakeMonitorTrapException ())))
                                              else
                                                (do
                                                  let w__72 ← (( do
                                                    (pure ((← do
                                                          if (((HaveEL EL3) : Bool) : Bool)
                                                          then
                                                            (do
                                                              let w__70 ← (( do
                                                                (ELUsingAArch32 EL3) ) : SailM Bool
                                                                )
                                                              (pure (((! w__70) : Bool))))
                                                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool)))
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
                                                          (AArch64_AArch32SystemAccessTrap EL3
                                                            (BitVec.toNat 0x05#8))))
                                                  else
                                                    (do
                                                      let w__76 ← (( do (DBGDTRTXext_read ()) ) :
                                                        SailM (BitVec 32) )
                                                      (R_set t w__76))))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__85 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         (pure ((← do
                                               (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                    then
                                      (do
                                        let w__79 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__79) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__83 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__83) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__85 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__94 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        if ((← do
                                             (pure ((← do
                                                   (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                        then
                                          (do
                                            let w__88 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__88) == 1#1) : Bool))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL3))
                              else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) : SailM Bool )
                      if (w__94 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__103 ← (( do
                            (pure ((← do
                                  if ((← do
                                       if ((← do
                                            if ((← do
                                                 (pure ((← do
                                                       (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                            then
                                              (do
                                                let w__97 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__97) == 1#1) : Bool))))
                                            else (pure false)) : Bool)
                                       then
                                         (do
                                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                                       else (pure false)) : Bool)
                                  then
                                    (do
                                      let w__101 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__101) : Bool))))
                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__103 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              let w__106 ← (( do
                                (pure ((← do
                                      if (((HaveEL EL3) : Bool) : Bool)
                                      then
                                        (do
                                          let w__104 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__104) : Bool))))
                                      else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__106 : Bool)
                              then
                                (do
                                  let w__109 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__108 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__108) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__109 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                              else
                                (do
                                  let w__112 ← (( do
                                    (pure ((← do
                                          if (((HaveEL EL3) : Bool) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL3))
                                          else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__112 : Bool)
                                  then
                                    (do
                                      let w__115 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__114 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__114) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__115 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch32_TakeMonitorTrapException ())))
                                  else
                                    (do
                                      let w__118 ← (( do
                                        (pure ((← do
                                              if (((HaveEL EL3) : Bool) : Bool)
                                              then
                                                (do
                                                  let w__116 ← (( do (ELUsingAArch32 EL3) ) :
                                                    SailM Bool )
                                                  (pure (((! w__116) : Bool))))
                                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__118 : Bool)
                                      then
                                        (do
                                          let w__121 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__120 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__120) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__121 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x05#8))))
                                      else
                                        (do
                                          let w__122 ← (( do (DBGDTRTXext_read ()) ) : SailM
                                            (BitVec 32) )
                                          (R_set t w__122))))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((__PSTATE_M != M32_Monitor) && (__SDCR_TDCC == 1#1)) : Bool)
                      then
                        (do
                          (AArch32_TakeMonitorTrapException ()))
                      else
                        (do
                          let w__123 ← (( do (DBGDTRTXext_read ()) ) : SailM (BitVec 32) )
                          (R_set t w__123)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def DBGOSDLR_SysRegRead32_c1e6447a93f7efb4 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TDOSA : (BitVec 1) := (_get_MDCR_EL2_Type_TDOSA w__1)
  let w__2 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  let __HDCR_TDOSA : (BitVec 1) := (_get_HDCR_Type_TDOSA w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__16 ← (( do
            if ((← do
                 if ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
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
                      else (pure false)) : Bool)
                 then
                   (do
                     let w__11 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                     (pure ((((_get_MDCR_EL3_Type_TDOSA w__11) == 1#1) : Bool))))
                 else (pure false)) : Bool)
            then
              (do
                if ((← do
                     (IsFeatureImplemented FEAT_DoubleLock)) : Bool)
                then (pure true)
                else
                  (do
                    (__IMPDEF_boolean "Trapped by MDCR_EL3.TDOSA")))
            else (pure false) ) : SailM Bool )
          if (w__16 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__26 ← (( do
                if ((← do
                     if ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__18 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__18) : Bool))))
                          else (pure false)) : Bool)
                     then
                       (do
                         let w__20 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                         let w__21 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                         (pure (((((_get_MDCR_EL2_Type_TDE w__20) +++ (_get_MDCR_EL2_Type_TDOSA
                                 w__21)) != 0b00#2) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    if ((← do
                         (IsFeatureImplemented FEAT_DoubleLock)) : Bool)
                    then (pure true)
                    else
                      (do
                        (__IMPDEF_boolean "Trapped by MDCR_EL2.TDOSA")))
                else (pure false) ) : SailM Bool )
              if (w__26 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
              else
                (do
                  let w__36 ← (( do
                    if ((← do
                         if ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) : Bool)
                         then
                           (do
                             let w__30 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                             let w__31 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                             (pure (((((_get_HDCR_Type_TDE w__30) +++ (_get_HDCR_Type_TDOSA w__31)) != 0b00#2) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        if ((← do
                             (IsFeatureImplemented FEAT_DoubleLock)) : Bool)
                        then (pure true)
                        else
                          (do
                            (__IMPDEF_boolean "Trapped by HDCR.TDOSA")))
                    else (pure false) ) : SailM Bool )
                  if (w__36 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                  else
                    (do
                      let w__44 ← (( do
                        if ((← do
                             if ((← do
                                  if (((HaveEL EL3) : Bool) : Bool)
                                  then
                                    (do
                                      let w__37 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__37) : Bool))))
                                  else (pure false)) : Bool)
                             then
                               (do
                                 let w__39 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                                 (pure ((((_get_MDCR_EL3_Type_TDOSA w__39) == 1#1) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            if ((← do
                                 (IsFeatureImplemented FEAT_DoubleLock)) : Bool)
                            then (pure true)
                            else
                              (do
                                (__IMPDEF_boolean "Trapped by MDCR_EL3.TDOSA")))
                        else (pure false) ) : SailM Bool )
                      if (w__44 : Bool)
                      then
                        (do
                          let w__47 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__46 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__46) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__47 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                      else
                        (do
                          let w__48 ← (( do (DBGOSDLR_read ()) ) : SailM (BitVec 32) )
                          let w__49 ← (( do (__get_DBGOSDLR w__48) ) : SailM (BitVec 32) )
                          (R_set t w__49))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__63 ← (( do
                if ((← do
                     if ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         (pure ((← do
                                               (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
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
                          else (pure false)) : Bool)
                     then
                       (do
                         let w__58 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                         (pure ((((_get_MDCR_EL3_Type_TDOSA w__58) == 1#1) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    if ((← do
                         (IsFeatureImplemented FEAT_DoubleLock)) : Bool)
                    then (pure true)
                    else
                      (do
                        (__IMPDEF_boolean "Trapped by MDCR_EL3.TDOSA")))
                else (pure false) ) : SailM Bool )
              if (w__63 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__71 ← (( do
                    if ((← do
                         if ((← do
                              if (((HaveEL EL3) : Bool) : Bool)
                              then
                                (do
                                  let w__64 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__64) : Bool))))
                              else (pure false)) : Bool)
                         then
                           (do
                             let w__66 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                             (pure ((((_get_MDCR_EL3_Type_TDOSA w__66) == 1#1) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        if ((← do
                             (IsFeatureImplemented FEAT_DoubleLock)) : Bool)
                        then (pure true)
                        else
                          (do
                            (__IMPDEF_boolean "Trapped by MDCR_EL3.TDOSA")))
                    else (pure false) ) : SailM Bool )
                  if (w__71 : Bool)
                  then
                    (do
                      let w__74 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__73 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__73) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__74 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                  else
                    (do
                      let w__75 ← (( do (DBGOSDLR_read ()) ) : SailM (BitVec 32) )
                      let w__76 ← (( do (__get_DBGOSDLR w__75) ) : SailM (BitVec 32) )
                      (R_set t w__76))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__77 ← (( do (DBGOSDLR_read ()) ) : SailM (BitVec 32) )
                  let w__78 ← (( do (__get_DBGOSDLR w__77) ) : SailM (BitVec 32) )
                  (R_set t w__78))
              else (pure (())))))


end ArmFull.Functions
