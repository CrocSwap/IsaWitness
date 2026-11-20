module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0054
public import ArmFull.Fn.M0082
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
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
def DBGDTRTXint_SysRegWrite32_bf0ab983b07d829c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  let __MDSCR_EL1_TDCC : (BitVec 1) := (_get_MDSCR_EL1_Type_TDCC w__1)
  let w__2 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
  let __DBGDSCRext_UDCCdis : (BitVec 1) := (_get_DBGDSCRext_Type_UDCCdis w__2)
  let w__3 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TDCC : (BitVec 1) := (_get_MDCR_EL2_Type_TDCC w__3)
  let w__4 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  let __HDCR_TDCC : (BitVec 1) := (_get_HDCR_Type_TDCC w__4)
  let w__5 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDCC : (BitVec 1) := (_get_MDCR_EL3_Type_TDCC w__5)
  let w__6 ← (( do readReg SDCR ) : SailM (BitVec 32) )
  let __SDCR_TDCC : (BitVec 1) := (_get_SDCR_Type_TDCC w__6)
  let w__7 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__7)
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_M : (BitVec 5) := w__8.M
  let w__9 ← (( do (Halted ()) ) : SailM Bool )
  if (w__9 : Bool)
  then
    (do
      let w__10 ← (( do (R_read t) ) : SailM (BitVec 32) )
      (DBGDTRTXint_write (Mk_DBGDTRTXint_Type w__10)))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          let w__12 ← (( do
            (pure ((← do
                  let w__11 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                  (pure (((! w__11) : Bool)))) && ((__MDSCR_EL1_TDCC == 1#1) : Bool))) ) : SailM
            Bool )
          if (w__12 : Bool)
          then
            (do
              let w__17 ← (( do
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
                    let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure ((((_get_HCR_EL2_Type_TGE w__16) == 1#1) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__17 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
              else
                (do
                  (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x05#8))))
          else
            (do
              let w__19 ← (( do
                (pure ((← do
                      (ELUsingAArch32 EL1)) && ((__DBGDSCRext_UDCCdis == 1#1) : Bool))) ) : SailM
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
                      let w__29 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 (ELUsingAArch32 EL2))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__28 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_HCR_Type_TGE w__28) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__29 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                      else sailThrow ((Error_Undefined ()))))
              else
                (do
                  let w__33 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__31 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__31) : Bool))))
                          else (pure false)) && ((__MDCR_EL2_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__33 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                  else
                    (do
                      let w__37 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HDCR_TDCC == 1#1) : Bool))) ) : SailM Bool )
                      if (w__37 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                      else
                        (do
                          let w__45 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     let w__39 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                     (pure (((! w__39) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                if ((← do
                                     let w__41 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     (pure ((((_get_HCR_EL2_Type_TGE w__41) == 1#1) : Bool)))) : Bool)
                                then (pure true)
                                else
                                  (do
                                    let w__42 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                                    let w__43 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_MDCR_EL2_Type_TDE w__42) +++ (_get_MDCR_EL2_Type_TDA
                                            w__43)) != 0b00#2) : Bool)))))
                            else (pure false) ) : SailM Bool )
                          if (w__45 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              let w__53 ← (( do
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
                                         let w__49 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                                         (pure ((((_get_HCR_Type_TGE w__49) == 1#1) : Bool)))) : Bool)
                                    then (pure true)
                                    else
                                      (do
                                        let w__50 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                                        let w__51 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                                        (pure (((((_get_HDCR_Type_TDE w__50) +++ (_get_HDCR_Type_TDA
                                                w__51)) != 0b00#2) : Bool)))))
                                else (pure false) ) : SailM Bool )
                              if (w__53 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                              else
                                (do
                                  let w__57 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (HaveEL EL3)) : Bool)
                                          then
                                            (do
                                              let w__55 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                Bool )
                                              (pure (((! w__55) : Bool))))
                                          else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool)))
                                    ) : SailM Bool )
                                  if (w__57 : Bool)
                                  then
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                                  else
                                    (do
                                      let w__61 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (HaveEL EL3)) : Bool)
                                              then
                                                (do
                                                  (ELUsingAArch32 EL3))
                                              else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__61 : Bool)
                                      then
                                        (do
                                          (AArch32_TakeMonitorTrapException ()))
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
                                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__65 : Bool)
                                          then
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x05#8)))
                                          else
                                            (do
                                              let w__66 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                              (DBGDTRTXint_write (Mk_DBGDTRTXint_Type w__66))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__70 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__68 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__68) : Bool))))
                      else (pure false)) && ((__MDCR_EL2_TDCC == 1#1) : Bool))) ) : SailM Bool )
              if (w__70 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
              else
                (do
                  let w__74 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HDCR_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__74 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                  else
                    (do
                      let w__80 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 let w__76 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                 (pure (((! w__76) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__78 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            let w__79 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            (pure (((((_get_MDCR_EL2_Type_TDE w__78) +++ (_get_MDCR_EL2_Type_TDA
                                    w__79)) != 0b00#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__80 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          let w__86 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     (ELUsingAArch32 EL2))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__84 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                                let w__85 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                                (pure (((((_get_HDCR_Type_TDE w__84) +++ (_get_HDCR_Type_TDA w__85)) != 0b00#2) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__86 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                          else
                            (do
                              let w__90 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          let w__88 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__88) : Bool))))
                                      else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__90 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                              else
                                (do
                                  let w__94 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (HaveEL EL3)) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL3))
                                          else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__94 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeMonitorTrapException ()))
                                  else
                                    (do
                                      let w__98 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (HaveEL EL3)) : Bool)
                                              then
                                                (do
                                                  let w__96 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                    Bool )
                                                  (pure (((! w__96) : Bool))))
                                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__98 : Bool)
                                      then
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                                      else
                                        (do
                                          let w__99 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                          (DBGDTRTXint_write (Mk_DBGDTRTXint_Type w__99))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__103 ← (( do
                    (pure ((← do
                          if ((← do
                               (HaveEL EL3)) : Bool)
                          then
                            (do
                              let w__101 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__101) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__103 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                  else
                    (do
                      let w__107 ← (( do
                        (pure ((← do
                              if ((← do
                                   (HaveEL EL3)) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL3))
                              else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) : SailM Bool )
                      if (w__107 : Bool)
                      then
                        (do
                          (AArch32_TakeMonitorTrapException ()))
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
                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__111 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              let w__112 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (DBGDTRTXint_write (Mk_DBGDTRTXint_Type w__112))))))
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
                          let w__113 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (DBGDTRTXint_write (Mk_DBGDTRTXint_Type w__113))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def DBGOSDLR_SysRegWrite32_d7c248a695fd43a4 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__17 ← (( do
            if ((← do
                 if ((← do
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
                      else (pure false)) : Bool)
                 then
                   (do
                     let w__12 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                     (pure ((((_get_MDCR_EL3_Type_TDOSA w__12) == 1#1) : Bool))))
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
          if (w__17 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__27 ← (( do
                if ((← do
                     if ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__19 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__19) : Bool))))
                          else (pure false)) : Bool)
                     then
                       (do
                         let w__21 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                         let w__22 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                         (pure (((((_get_MDCR_EL2_Type_TDE w__21) +++ (_get_MDCR_EL2_Type_TDOSA
                                 w__22)) != 0b00#2) : Bool))))
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
              if (w__27 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
              else
                (do
                  let w__37 ← (( do
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
                             let w__31 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                             let w__32 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                             (pure (((((_get_HDCR_Type_TDE w__31) +++ (_get_HDCR_Type_TDOSA w__32)) != 0b00#2) : Bool))))
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
                  if (w__37 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                  else
                    (do
                      let w__46 ← (( do
                        if ((← do
                             if ((← do
                                  if ((← do
                                       (HaveEL EL3)) : Bool)
                                  then
                                    (do
                                      let w__39 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__39) : Bool))))
                                  else (pure false)) : Bool)
                             then
                               (do
                                 let w__41 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                                 (pure ((((_get_MDCR_EL3_Type_TDOSA w__41) == 1#1) : Bool))))
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
                          let w__50 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (DBGOSDLR_write (Mk_DBGOSDLR_Type w__50)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__65 ← (( do
                if ((← do
                     if ((← do
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
                                        let w__54 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__54) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__58 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__58) : Bool))))
                          else (pure false)) : Bool)
                     then
                       (do
                         let w__60 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                         (pure ((((_get_MDCR_EL3_Type_TDOSA w__60) == 1#1) : Bool))))
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
              if (w__65 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__74 ← (( do
                    if ((← do
                         if ((← do
                              if ((← do
                                   (HaveEL EL3)) : Bool)
                              then
                                (do
                                  let w__67 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__67) : Bool))))
                              else (pure false)) : Bool)
                         then
                           (do
                             let w__69 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                             (pure ((((_get_MDCR_EL3_Type_TDOSA w__69) == 1#1) : Bool))))
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
                  if (w__74 : Bool)
                  then
                    (do
                      let w__77 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__76 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__76) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__77 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                  else
                    (do
                      let w__78 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (DBGOSDLR_write (Mk_DBGOSDLR_Type w__78)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__79 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (DBGOSDLR_write (Mk_DBGOSDLR_Type w__79)))
              else (pure (())))))


end ArmFull.Functions
