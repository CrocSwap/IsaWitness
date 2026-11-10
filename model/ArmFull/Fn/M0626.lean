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
import ArmFull.Fn.M0053
import ArmFull.Fn.M0086
import ArmFull.Fn.M0100
import ArmFull.Fn.M0140
import ArmFull.Fn.M0145
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0203
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
def DBGDRAR_SysRegRead32_421a9884bf20a229 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
      let w__7 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
      (R_set t (Sail.BitVec.extractLsb (__get_DBGDRAR w__7) 31 0)))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          let w__16 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                            then
                              (do
                                let w__10 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__10) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__14 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__14) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
          if (w__16 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__18 ← (( do
                (pure ((← do
                      let w__17 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                      (pure (((! w__17) : Bool)))) && ((__MDSCR_EL1_TDCC == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__18 : Bool)
              then
                (do
                  let w__23 ← (( do
                    if ((← do
                         if ((← do
                              (EL2Enabled ())) : Bool)
                         then
                           (do
                             let w__20 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                             (pure (((! w__20) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__22 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure ((((_get_HCR_EL2_Type_TGE w__22) == 1#1) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__23 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                  else
                    (do
                      (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x05#8))))
              else
                (do
                  let w__25 ← (( do
                    (pure ((← do
                          (ELUsingAArch32 EL1)) && ((__DBGDSCRext_UDCCdis == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__25 : Bool)
                  then
                    (do
                      let w__30 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 let w__27 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                 (pure (((! w__27) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__29 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                            (pure ((((_get_HCR_EL2_Type_TGE w__29) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__30 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          let w__35 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     (ELUsingAArch32 EL2))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__34 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_HCR_Type_TGE w__34) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__35 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                          else sailThrow ((Error_Undefined ()))))
                  else
                    (do
                      let w__43 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 let w__37 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                 (pure (((! w__37) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            if ((← do
                                 let w__39 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 (pure ((((_get_HCR_EL2_Type_TGE w__39) == 1#1) : Bool)))) : Bool)
                            then (pure true)
                            else
                              (do
                                let w__40 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                                let w__41 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                                (pure (((((_get_MDCR_EL2_Type_TDE w__40) +++ (_get_MDCR_EL2_Type_TDRA
                                        w__41)) != 0b00#2) : Bool)))))
                        else (pure false) ) : SailM Bool )
                      if (w__43 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          let w__51 ← (( do
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
                                     let w__47 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                                     (pure ((((_get_HCR_Type_TGE w__47) == 1#1) : Bool)))) : Bool)
                                then (pure true)
                                else
                                  (do
                                    let w__48 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                                    let w__49 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                                    (pure (((((_get_HDCR_Type_TDE w__48) +++ (_get_HDCR_Type_TDRA
                                            w__49)) != 0b00#2) : Bool)))))
                            else (pure false) ) : SailM Bool )
                          if (w__51 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                          else
                            (do
                              let w__54 ← (( do
                                (pure ((← do
                                      if (((HaveEL EL3) : Bool) : Bool)
                                      then
                                        (do
                                          let w__52 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__52) : Bool))))
                                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__54 : Bool)
                              then
                                (do
                                  let w__57 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__56 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__56) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__57 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                              else
                                (do
                                  let w__58 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
                                  (R_set t (Sail.BitVec.extractLsb (__get_DBGDRAR w__58) 31 0)))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__67 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                then
                                  (do
                                    let w__61 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__61) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__65 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__65) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
              if (w__67 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__73 ← (( do
                    if ((← do
                         if ((← do
                              (EL2Enabled ())) : Bool)
                         then
                           (do
                             let w__69 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                             (pure (((! w__69) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__71 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        let w__72 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_MDCR_EL2_Type_TDE w__71) +++ (_get_MDCR_EL2_Type_TDRA w__72)) != 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__73 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                  else
                    (do
                      let w__79 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 (ELUsingAArch32 EL2))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__77 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                            let w__78 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                            (pure (((((_get_HDCR_Type_TDE w__77) +++ (_get_HDCR_Type_TDRA w__78)) != 0b00#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__79 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                      else
                        (do
                          let w__82 ← (( do
                            (pure ((← do
                                  if (((HaveEL EL3) : Bool) : Bool)
                                  then
                                    (do
                                      let w__80 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__80) : Bool))))
                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__82 : Bool)
                          then
                            (do
                              let w__85 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__84 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__84) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__85 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                          else
                            (do
                              let w__86 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
                              (R_set t (Sail.BitVec.extractLsb (__get_DBGDRAR w__86) 31 0)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__95 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         (pure ((← do
                                               (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                    then
                                      (do
                                        let w__89 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__89) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__93 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__93) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__95 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__98 ← (( do
                        (pure ((← do
                              if (((HaveEL EL3) : Bool) : Bool)
                              then
                                (do
                                  let w__96 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__96) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__98 : Bool)
                      then
                        (do
                          let w__101 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__100 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__100) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__101 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                      else
                        (do
                          let w__102 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
                          (R_set t (Sail.BitVec.extractLsb (__get_DBGDRAR w__102) 31 0)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__103 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
                      (R_set t (Sail.BitVec.extractLsb (__get_DBGDRAR w__103) 31 0)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def DBGDSAR_SysRegRead32_94ff484a75802dcb (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
      let w__7 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
      (R_set t (Sail.BitVec.extractLsb (__get_DBGDSAR w__7) 31 0)))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          let w__16 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                            then
                              (do
                                let w__10 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__10) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__14 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__14) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
          if (w__16 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__18 ← (( do
                (pure ((← do
                      let w__17 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                      (pure (((! w__17) : Bool)))) && ((__MDSCR_EL1_TDCC == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__18 : Bool)
              then
                (do
                  let w__23 ← (( do
                    if ((← do
                         if ((← do
                              (EL2Enabled ())) : Bool)
                         then
                           (do
                             let w__20 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                             (pure (((! w__20) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__22 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure ((((_get_HCR_EL2_Type_TGE w__22) == 1#1) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__23 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                  else
                    (do
                      (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x05#8))))
              else
                (do
                  let w__25 ← (( do
                    (pure ((← do
                          (ELUsingAArch32 EL1)) && ((__DBGDSCRext_UDCCdis == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__25 : Bool)
                  then
                    (do
                      let w__30 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 let w__27 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                 (pure (((! w__27) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__29 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                            (pure ((((_get_HCR_EL2_Type_TGE w__29) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__30 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          let w__35 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     (ELUsingAArch32 EL2))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__34 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_HCR_Type_TGE w__34) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__35 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                          else sailThrow ((Error_Undefined ()))))
                  else
                    (do
                      let w__43 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 let w__37 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                 (pure (((! w__37) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            if ((← do
                                 let w__39 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 (pure ((((_get_HCR_EL2_Type_TGE w__39) == 1#1) : Bool)))) : Bool)
                            then (pure true)
                            else
                              (do
                                let w__40 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                                let w__41 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                                (pure (((((_get_MDCR_EL2_Type_TDE w__40) +++ (_get_MDCR_EL2_Type_TDRA
                                        w__41)) != 0b00#2) : Bool)))))
                        else (pure false) ) : SailM Bool )
                      if (w__43 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          let w__51 ← (( do
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
                                     let w__47 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                                     (pure ((((_get_HCR_Type_TGE w__47) == 1#1) : Bool)))) : Bool)
                                then (pure true)
                                else
                                  (do
                                    let w__48 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                                    let w__49 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                                    (pure (((((_get_HDCR_Type_TDE w__48) +++ (_get_HDCR_Type_TDRA
                                            w__49)) != 0b00#2) : Bool)))))
                            else (pure false) ) : SailM Bool )
                          if (w__51 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                          else
                            (do
                              let w__54 ← (( do
                                (pure ((← do
                                      if (((HaveEL EL3) : Bool) : Bool)
                                      then
                                        (do
                                          let w__52 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__52) : Bool))))
                                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__54 : Bool)
                              then
                                (do
                                  let w__57 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__56 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__56) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__57 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                              else
                                (do
                                  let w__58 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
                                  (R_set t (Sail.BitVec.extractLsb (__get_DBGDSAR w__58) 31 0)))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__67 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                then
                                  (do
                                    let w__61 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__61) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__65 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__65) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
              if (w__67 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__73 ← (( do
                    if ((← do
                         if ((← do
                              (EL2Enabled ())) : Bool)
                         then
                           (do
                             let w__69 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                             (pure (((! w__69) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__71 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        let w__72 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_MDCR_EL2_Type_TDE w__71) +++ (_get_MDCR_EL2_Type_TDRA w__72)) != 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__73 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                  else
                    (do
                      let w__79 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 (ELUsingAArch32 EL2))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__77 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                            let w__78 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                            (pure (((((_get_HDCR_Type_TDE w__77) +++ (_get_HDCR_Type_TDRA w__78)) != 0b00#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__79 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                      else
                        (do
                          let w__82 ← (( do
                            (pure ((← do
                                  if (((HaveEL EL3) : Bool) : Bool)
                                  then
                                    (do
                                      let w__80 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__80) : Bool))))
                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__82 : Bool)
                          then
                            (do
                              let w__85 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__84 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__84) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__85 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                          else
                            (do
                              let w__86 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
                              (R_set t (Sail.BitVec.extractLsb (__get_DBGDSAR w__86) 31 0)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__95 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         (pure ((← do
                                               (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                    then
                                      (do
                                        let w__89 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__89) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__93 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__93) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__95 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__98 ← (( do
                        (pure ((← do
                              if (((HaveEL EL3) : Bool) : Bool)
                              then
                                (do
                                  let w__96 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__96) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__98 : Bool)
                      then
                        (do
                          let w__101 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__100 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__100) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__101 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                      else
                        (do
                          let w__102 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
                          (R_set t (Sail.BitVec.extractLsb (__get_DBGDSAR w__102) 31 0)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__103 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
                      (R_set t (Sail.BitVec.extractLsb (__get_DBGDSAR w__103) 31 0)))
                  else (pure (()))))))


end ArmFull.Functions
