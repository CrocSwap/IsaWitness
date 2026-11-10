import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0042
import ArmFull.Fn.M0047
import ArmFull.Fn.M0100
import ArmFull.Fn.M0116
import ArmFull.Fn.M0141
import ArmFull.Fn.M0145
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
def DBGDSCRext_SysRegRead32_bbe7b972eea0caec (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                          let w__29 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
                          (R_set t (__get_DBGDSCRext w__29)))))))
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
                      let w__45 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
                      (R_set t (__get_DBGDSCRext w__45)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__46 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
                  (R_set t (__get_DBGDSCRext w__46)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DBGDSCRint_SysRegRead32_4d6240b644e5e8d8 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDCC : (BitVec 1) := (_get_MDCR_EL3_Type_TDCC w__1)
  let w__2 ← (( do readReg SDCR ) : SailM (BitVec 32) )
  let __SDCR_TDCC : (BitVec 1) := (_get_SDCR_Type_TDCC w__2)
  let w__3 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__3)
  let w__4 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  let __MDSCR_EL1_TDCC : (BitVec 1) := (_get_MDSCR_EL1_Type_TDCC w__4)
  let w__5 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
  let __DBGDSCRext_UDCCdis : (BitVec 1) := (_get_DBGDSCRext_Type_UDCCdis w__5)
  let w__6 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TDCC : (BitVec 1) := (_get_MDCR_EL2_Type_TDCC w__6)
  let w__7 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  let __HDCR_TDCC : (BitVec 1) := (_get_HDCR_Type_TDCC w__7)
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_M : (BitVec 5) := w__8.M
  let w__11 ← (( do
    if ((← do
         (Halted ())) : Bool)
    then
      (do
        (ConstrainUnpredictableBool Unpredictable_IGNORETRAPINDEBUG))
    else (pure false) ) : SailM Bool )
  if (w__11 : Bool)
  then
    (do
      if ((t == 15) : Bool)
      then
        (do
          let w__12 ← (( do (DBGDSCRint_read ()) ) : SailM (BitVec 32) )
          let split_vec := (Sail.BitVec.extractLsb w__12 31 28)
          let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__13 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
          let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__14 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
          let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__15 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
          let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__16 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
      else
        (do
          let w__17 ← (( do (DBGDSCRint_read ()) ) : SailM (BitVec 32) )
          (R_set t (__get_DBGDSCRint w__17))))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          let w__26 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                            then
                              (do
                                let w__20 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__20) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__24 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__24) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
          if (w__26 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__35 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                then
                                  (do
                                    let w__29 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__29) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL3))
                      else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) : SailM Bool )
              if (w__35 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
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
                      let w__46 ← (( do
                        (pure ((← do
                              let w__45 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                              (pure (((! w__45) : Bool)))) && ((__MDSCR_EL1_TDCC == 1#1) : Bool))) )
                        : SailM Bool )
                      if (w__46 : Bool)
                      then
                        (do
                          let w__51 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     let w__48 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                     (pure (((! w__48) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__50 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                (pure ((((_get_HCR_EL2_Type_TGE w__50) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__51 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x05#8))))
                      else
                        (do
                          let w__53 ← (( do
                            (pure ((← do
                                  (ELUsingAArch32 EL1)) && ((__DBGDSCRext_UDCCdis == 1#1) : Bool)))
                            ) : SailM Bool )
                          if (w__53 : Bool)
                          then
                            (do
                              let w__58 ← (( do
                                if ((← do
                                     if ((← do
                                          (EL2Enabled ())) : Bool)
                                     then
                                       (do
                                         let w__55 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                         (pure (((! w__55) : Bool))))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__57 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure ((((_get_HCR_EL2_Type_TGE w__57) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__58 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                              else
                                (do
                                  let w__63 ← (( do
                                    if ((← do
                                         if ((← do
                                              (EL2Enabled ())) : Bool)
                                         then
                                           (do
                                             (ELUsingAArch32 EL2))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__62 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_HCR_Type_TGE w__62) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__63 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                                  else sailThrow ((Error_Undefined ()))))
                          else
                            (do
                              let w__67 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          let w__65 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                          (pure (((! w__65) : Bool))))
                                      else (pure false)) && ((__MDCR_EL2_TDCC == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__67 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                              else
                                (do
                                  let w__71 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (EL2Enabled ())) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL2))
                                          else (pure false)) && ((__HDCR_TDCC == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__71 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                                  else
                                    (do
                                      let w__79 ← (( do
                                        if ((← do
                                             if ((← do
                                                  (EL2Enabled ())) : Bool)
                                             then
                                               (do
                                                 let w__73 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                   Bool )
                                                 (pure (((! w__73) : Bool))))
                                             else (pure false)) : Bool)
                                        then
                                          (do
                                            if ((← do
                                                 let w__75 ← (( do readReg HCR_EL2 ) : SailM
                                                   (BitVec 64) )
                                                 (pure ((((_get_HCR_EL2_Type_TGE w__75) == 1#1) : Bool)))) : Bool)
                                            then (pure true)
                                            else
                                              (do
                                                let w__76 ← (( do readReg MDCR_EL2 ) : SailM
                                                  (BitVec 64) )
                                                let w__77 ← (( do readReg MDCR_EL2 ) : SailM
                                                  (BitVec 64) )
                                                (pure (((((_get_MDCR_EL2_Type_TDE w__76) +++ (_get_MDCR_EL2_Type_TDA
                                                        w__77)) != 0b00#2) : Bool)))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__79 : Bool)
                                      then
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                                      else
                                        (do
                                          let w__87 ← (( do
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
                                                     let w__83 ← (( do (HCR_read ()) ) : SailM
                                                       (BitVec 32) )
                                                     (pure ((((_get_HCR_Type_TGE w__83) == 1#1) : Bool)))) : Bool)
                                                then (pure true)
                                                else
                                                  (do
                                                    let w__84 ← (( do (HDCR_read ()) ) : SailM
                                                      (BitVec 32) )
                                                    let w__85 ← (( do (HDCR_read ()) ) : SailM
                                                      (BitVec 32) )
                                                    (pure (((((_get_HDCR_Type_TDE w__84) +++ (_get_HDCR_Type_TDA
                                                            w__85)) != 0b00#2) : Bool)))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__87 : Bool)
                                          then
                                            (do
                                              (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                                          else
                                            (do
                                              let w__90 ← (( do
                                                (pure ((← do
                                                      if (((HaveEL EL3) : Bool) : Bool)
                                                      then
                                                        (do
                                                          let w__88 ← (( do (ELUsingAArch32 EL3) )
                                                            : SailM Bool )
                                                          (pure (((! w__88) : Bool))))
                                                      else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__90 : Bool)
                                              then
                                                (do
                                                  let w__93 ← (( do
                                                    if ((← do
                                                         (Halted ())) : Bool)
                                                    then
                                                      (do
                                                        let w__92 ← (( do (EDSCR_read ()) ) :
                                                          SailM (BitVec 32) )
                                                        (pure ((((_get_EDSCR_Type_SDD w__92) == 1#1) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__93 : Bool)
                                                  then sailThrow ((Error_Undefined ()))
                                                  else
                                                    (do
                                                      (AArch64_AArch32SystemAccessTrap EL3
                                                        (BitVec.toNat 0x05#8))))
                                              else
                                                (do
                                                  let w__96 ← (( do
                                                    (pure ((← do
                                                          if (((HaveEL EL3) : Bool) : Bool)
                                                          then
                                                            (do
                                                              (ELUsingAArch32 EL3))
                                                          else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool)))
                                                    ) : SailM Bool )
                                                  if (w__96 : Bool)
                                                  then
                                                    (do
                                                      let w__99 ← (( do
                                                        if ((← do
                                                             (Halted ())) : Bool)
                                                        then
                                                          (do
                                                            let w__98 ← (( do (EDSCR_read ()) ) :
                                                              SailM (BitVec 32) )
                                                            (pure ((((_get_EDSCR_Type_SDD w__98) == 1#1) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__99 : Bool)
                                                      then sailThrow ((Error_Undefined ()))
                                                      else
                                                        (do
                                                          (AArch32_TakeMonitorTrapException ())))
                                                  else
                                                    (do
                                                      let w__102 ← (( do
                                                        (pure ((← do
                                                              if (((HaveEL EL3) : Bool) : Bool)
                                                              then
                                                                (do
                                                                  let w__100 ← (( do
                                                                    (ELUsingAArch32 EL3) ) : SailM
                                                                    Bool )
                                                                  (pure (((! w__100) : Bool))))
                                                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool)))
                                                        ) : SailM Bool )
                                                      if (w__102 : Bool)
                                                      then
                                                        (do
                                                          let w__105 ← (( do
                                                            if ((← do
                                                                 (Halted ())) : Bool)
                                                            then
                                                              (do
                                                                let w__104 ← (( do (EDSCR_read ())
                                                                  ) : SailM (BitVec 32) )
                                                                (pure ((((_get_EDSCR_Type_SDD w__104) == 1#1) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__105 : Bool)
                                                          then sailThrow ((Error_Undefined ()))
                                                          else
                                                            (do
                                                              (AArch64_AArch32SystemAccessTrap EL3
                                                                (BitVec.toNat 0x05#8))))
                                                      else
                                                        (do
                                                          if ((t == 15) : Bool)
                                                          then
                                                            (do
                                                              let w__106 ← (( do
                                                                (DBGDSCRint_read ()) ) : SailM
                                                                (BitVec 32) )
                                                              let split_vec :=
                                                                (Sail.BitVec.extractLsb w__106 31 28)
                                                              let w__107 ← (( do readReg PSTATE )
                                                                : SailM ProcState )
                                                              writeReg PSTATE { w__107 with N := (Sail.BitVec.extractLsb
                                                                  split_vec 3 3) }
                                                              let w__108 ← (( do readReg PSTATE )
                                                                : SailM ProcState )
                                                              writeReg PSTATE { w__108 with Z := (Sail.BitVec.extractLsb
                                                                  split_vec 2 2) }
                                                              let w__109 ← (( do readReg PSTATE )
                                                                : SailM ProcState )
                                                              writeReg PSTATE { w__109 with C := (Sail.BitVec.extractLsb
                                                                  split_vec 1 1) }
                                                              let w__110 ← (( do readReg PSTATE )
                                                                : SailM ProcState )
                                                              writeReg PSTATE { w__110 with V := (Sail.BitVec.extractLsb
                                                                  split_vec 0 0) })
                                                          else
                                                            (do
                                                              let w__111 ← (( do
                                                                (DBGDSCRint_read ()) ) : SailM
                                                                (BitVec 32) )
                                                              (R_set t (__get_DBGDSCRint w__111))))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__120 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                then
                                  (do
                                    let w__114 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__114) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__118 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__118) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
              if (w__120 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__129 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         (pure ((← do
                                               (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                    then
                                      (do
                                        let w__123 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__123) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL3))
                          else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__129 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__138 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        if ((← do
                                             (pure ((← do
                                                   (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                        then
                                          (do
                                            let w__132 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__132) == 1#1) : Bool))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  let w__136 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__136) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__138 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__142 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__140 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                      (pure (((! w__140) : Bool))))
                                  else (pure false)) && ((__MDCR_EL2_TDCC == 1#1) : Bool))) ) :
                            SailM Bool )
                          if (w__142 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              let w__146 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HDCR_TDCC == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__146 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                              else
                                (do
                                  let w__152 ← (( do
                                    if ((← do
                                         if ((← do
                                              (EL2Enabled ())) : Bool)
                                         then
                                           (do
                                             let w__148 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                               Bool )
                                             (pure (((! w__148) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__150 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64)
                                          )
                                        let w__151 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64)
                                          )
                                        (pure (((((_get_MDCR_EL2_Type_TDE w__150) +++ (_get_MDCR_EL2_Type_TDA
                                                w__151)) != 0b00#2) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__152 : Bool)
                                  then
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                                  else
                                    (do
                                      let w__158 ← (( do
                                        if ((← do
                                             if ((← do
                                                  (EL2Enabled ())) : Bool)
                                             then
                                               (do
                                                 (ELUsingAArch32 EL2))
                                             else (pure false)) : Bool)
                                        then
                                          (do
                                            let w__156 ← (( do (HDCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            let w__157 ← (( do (HDCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure (((((_get_HDCR_Type_TDE w__156) +++ (_get_HDCR_Type_TDA
                                                    w__157)) != 0b00#2) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__158 : Bool)
                                      then
                                        (do
                                          (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                                      else
                                        (do
                                          let w__161 ← (( do
                                            (pure ((← do
                                                  if (((HaveEL EL3) : Bool) : Bool)
                                                  then
                                                    (do
                                                      let w__159 ← (( do (ELUsingAArch32 EL3) ) :
                                                        SailM Bool )
                                                      (pure (((! w__159) : Bool))))
                                                  else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__161 : Bool)
                                          then
                                            (do
                                              let w__164 ← (( do
                                                if ((← do
                                                     (Halted ())) : Bool)
                                                then
                                                  (do
                                                    let w__163 ← (( do (EDSCR_read ()) ) : SailM
                                                      (BitVec 32) )
                                                    (pure ((((_get_EDSCR_Type_SDD w__163) == 1#1) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__164 : Bool)
                                              then sailThrow ((Error_Undefined ()))
                                              else
                                                (do
                                                  (AArch64_AArch32SystemAccessTrap EL3
                                                    (BitVec.toNat 0x05#8))))
                                          else
                                            (do
                                              let w__167 ← (( do
                                                (pure ((← do
                                                      if (((HaveEL EL3) : Bool) : Bool)
                                                      then
                                                        (do
                                                          (ELUsingAArch32 EL3))
                                                      else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__167 : Bool)
                                              then
                                                (do
                                                  let w__170 ← (( do
                                                    if ((← do
                                                         (Halted ())) : Bool)
                                                    then
                                                      (do
                                                        let w__169 ← (( do (EDSCR_read ()) ) :
                                                          SailM (BitVec 32) )
                                                        (pure ((((_get_EDSCR_Type_SDD w__169) == 1#1) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__170 : Bool)
                                                  then sailThrow ((Error_Undefined ()))
                                                  else
                                                    (do
                                                      (AArch32_TakeMonitorTrapException ())))
                                              else
                                                (do
                                                  let w__173 ← (( do
                                                    (pure ((← do
                                                          if (((HaveEL EL3) : Bool) : Bool)
                                                          then
                                                            (do
                                                              let w__171 ← (( do
                                                                (ELUsingAArch32 EL3) ) : SailM Bool
                                                                )
                                                              (pure (((! w__171) : Bool))))
                                                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool)))
                                                    ) : SailM Bool )
                                                  if (w__173 : Bool)
                                                  then
                                                    (do
                                                      let w__176 ← (( do
                                                        if ((← do
                                                             (Halted ())) : Bool)
                                                        then
                                                          (do
                                                            let w__175 ← (( do (EDSCR_read ()) ) :
                                                              SailM (BitVec 32) )
                                                            (pure ((((_get_EDSCR_Type_SDD w__175) == 1#1) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__176 : Bool)
                                                      then sailThrow ((Error_Undefined ()))
                                                      else
                                                        (do
                                                          (AArch64_AArch32SystemAccessTrap EL3
                                                            (BitVec.toNat 0x05#8))))
                                                  else
                                                    (do
                                                      if ((t == 15) : Bool)
                                                      then
                                                        (do
                                                          let w__177 ← (( do (DBGDSCRint_read ())
                                                            ) : SailM (BitVec 32) )
                                                          let split_vec :=
                                                            (Sail.BitVec.extractLsb w__177 31 28)
                                                          let w__178 ← (( do readReg PSTATE ) :
                                                            SailM ProcState )
                                                          writeReg PSTATE { w__178 with N := (Sail.BitVec.extractLsb
                                                              split_vec 3 3) }
                                                          let w__179 ← (( do readReg PSTATE ) :
                                                            SailM ProcState )
                                                          writeReg PSTATE { w__179 with Z := (Sail.BitVec.extractLsb
                                                              split_vec 2 2) }
                                                          let w__180 ← (( do readReg PSTATE ) :
                                                            SailM ProcState )
                                                          writeReg PSTATE { w__180 with C := (Sail.BitVec.extractLsb
                                                              split_vec 1 1) }
                                                          let w__181 ← (( do readReg PSTATE ) :
                                                            SailM ProcState )
                                                          writeReg PSTATE { w__181 with V := (Sail.BitVec.extractLsb
                                                              split_vec 0 0) })
                                                      else
                                                        (do
                                                          let w__182 ← (( do (DBGDSCRint_read ())
                                                            ) : SailM (BitVec 32) )
                                                          (R_set t (__get_DBGDSCRint w__182))))))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__191 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         (pure ((← do
                                               (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                    then
                                      (do
                                        let w__185 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__185) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__189 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__189) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__191 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__200 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        if ((← do
                                             (pure ((← do
                                                   (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                        then
                                          (do
                                            let w__194 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__194) == 1#1) : Bool))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL3))
                              else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) : SailM Bool )
                      if (w__200 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__209 ← (( do
                            (pure ((← do
                                  if ((← do
                                       if ((← do
                                            if ((← do
                                                 (pure ((← do
                                                       (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                            then
                                              (do
                                                let w__203 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__203) == 1#1) : Bool))))
                                            else (pure false)) : Bool)
                                       then
                                         (do
                                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                                       else (pure false)) : Bool)
                                  then
                                    (do
                                      let w__207 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__207) : Bool))))
                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__209 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              let w__212 ← (( do
                                (pure ((← do
                                      if (((HaveEL EL3) : Bool) : Bool)
                                      then
                                        (do
                                          let w__210 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__210) : Bool))))
                                      else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__212 : Bool)
                              then
                                (do
                                  let w__215 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__214 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__214) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__215 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                              else
                                (do
                                  let w__218 ← (( do
                                    (pure ((← do
                                          if (((HaveEL EL3) : Bool) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL3))
                                          else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__218 : Bool)
                                  then
                                    (do
                                      let w__221 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__220 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__220) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__221 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch32_TakeMonitorTrapException ())))
                                  else
                                    (do
                                      let w__224 ← (( do
                                        (pure ((← do
                                              if (((HaveEL EL3) : Bool) : Bool)
                                              then
                                                (do
                                                  let w__222 ← (( do (ELUsingAArch32 EL3) ) :
                                                    SailM Bool )
                                                  (pure (((! w__222) : Bool))))
                                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__224 : Bool)
                                      then
                                        (do
                                          let w__227 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__226 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__226) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__227 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x05#8))))
                                      else
                                        (do
                                          if ((t == 15) : Bool)
                                          then
                                            (do
                                              let w__228 ← (( do (DBGDSCRint_read ()) ) : SailM
                                                (BitVec 32) )
                                              let split_vec := (Sail.BitVec.extractLsb w__228 31 28)
                                              let w__229 ← (( do readReg PSTATE ) : SailM
                                                ProcState )
                                              writeReg PSTATE { w__229 with N := (Sail.BitVec.extractLsb
                                                  split_vec 3 3) }
                                              let w__230 ← (( do readReg PSTATE ) : SailM
                                                ProcState )
                                              writeReg PSTATE { w__230 with Z := (Sail.BitVec.extractLsb
                                                  split_vec 2 2) }
                                              let w__231 ← (( do readReg PSTATE ) : SailM
                                                ProcState )
                                              writeReg PSTATE { w__231 with C := (Sail.BitVec.extractLsb
                                                  split_vec 1 1) }
                                              let w__232 ← (( do readReg PSTATE ) : SailM
                                                ProcState )
                                              writeReg PSTATE { w__232 with V := (Sail.BitVec.extractLsb
                                                  split_vec 0 0) })
                                          else
                                            (do
                                              let w__233 ← (( do (DBGDSCRint_read ()) ) : SailM
                                                (BitVec 32) )
                                              (R_set t (__get_DBGDSCRint w__233))))))))))
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
                          if ((t == 15) : Bool)
                          then
                            (do
                              let w__234 ← (( do (DBGDSCRint_read ()) ) : SailM (BitVec 32) )
                              let split_vec := (Sail.BitVec.extractLsb w__234 31 28)
                              let w__235 ← (( do readReg PSTATE ) : SailM ProcState )
                              writeReg PSTATE { w__235 with N := (Sail.BitVec.extractLsb split_vec 3
                                  3) }
                              let w__236 ← (( do readReg PSTATE ) : SailM ProcState )
                              writeReg PSTATE { w__236 with Z := (Sail.BitVec.extractLsb split_vec 2
                                  2) }
                              let w__237 ← (( do readReg PSTATE ) : SailM ProcState )
                              writeReg PSTATE { w__237 with C := (Sail.BitVec.extractLsb split_vec 1
                                  1) }
                              let w__238 ← (( do readReg PSTATE ) : SailM ProcState )
                              writeReg PSTATE { w__238 with V := (Sail.BitVec.extractLsb split_vec 0
                                  0) })
                          else
                            (do
                              let w__239 ← (( do (DBGDSCRint_read ()) ) : SailM (BitVec 32) )
                              (R_set t (__get_DBGDSCRint w__239)))))
                  else (pure (()))))))


end ArmFull.Functions
