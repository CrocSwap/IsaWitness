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
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0116
public import ArmFull.Fn.M0141
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0202
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
                          let w__31 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
                          (R_set t (__get_DBGDSCRext w__31)))))))
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
                      let w__49 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
                      (R_set t (__get_DBGDSCRext w__49)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__50 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
                  (R_set t (__get_DBGDSCRext w__50)))
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
          let w__27 ← (( do
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
                                let w__21 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__21) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__25 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__25) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
          if (w__27 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__37 ← (( do
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
                                    let w__31 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__31) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL3))
                      else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) : SailM Bool )
              if (w__37 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
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
                      let w__49 ← (( do
                        (pure ((← do
                              let w__48 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                              (pure (((! w__48) : Bool)))) && ((__MDSCR_EL1_TDCC == 1#1) : Bool))) )
                        : SailM Bool )
                      if (w__49 : Bool)
                      then
                        (do
                          let w__54 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     let w__51 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                     (pure (((! w__51) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__53 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                (pure ((((_get_HCR_EL2_Type_TGE w__53) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__54 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x05#8))))
                      else
                        (do
                          let w__56 ← (( do
                            (pure ((← do
                                  (ELUsingAArch32 EL1)) && ((__DBGDSCRext_UDCCdis == 1#1) : Bool)))
                            ) : SailM Bool )
                          if (w__56 : Bool)
                          then
                            (do
                              let w__61 ← (( do
                                if ((← do
                                     if ((← do
                                          (EL2Enabled ())) : Bool)
                                     then
                                       (do
                                         let w__58 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                         (pure (((! w__58) : Bool))))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__60 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure ((((_get_HCR_EL2_Type_TGE w__60) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__61 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                              else
                                (do
                                  let w__66 ← (( do
                                    if ((← do
                                         if ((← do
                                              (EL2Enabled ())) : Bool)
                                         then
                                           (do
                                             (ELUsingAArch32 EL2))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__65 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_HCR_Type_TGE w__65) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__66 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                                  else sailThrow ((Error_Undefined ()))))
                          else
                            (do
                              let w__70 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          let w__68 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                          (pure (((! w__68) : Bool))))
                                      else (pure false)) && ((__MDCR_EL2_TDCC == 1#1) : Bool))) ) :
                                SailM Bool )
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
                                          else (pure false)) && ((__HDCR_TDCC == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__74 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                                  else
                                    (do
                                      let w__82 ← (( do
                                        if ((← do
                                             if ((← do
                                                  (EL2Enabled ())) : Bool)
                                             then
                                               (do
                                                 let w__76 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                   Bool )
                                                 (pure (((! w__76) : Bool))))
                                             else (pure false)) : Bool)
                                        then
                                          (do
                                            if ((← do
                                                 let w__78 ← (( do readReg HCR_EL2 ) : SailM
                                                   (BitVec 64) )
                                                 (pure ((((_get_HCR_EL2_Type_TGE w__78) == 1#1) : Bool)))) : Bool)
                                            then (pure true)
                                            else
                                              (do
                                                let w__79 ← (( do readReg MDCR_EL2 ) : SailM
                                                  (BitVec 64) )
                                                let w__80 ← (( do readReg MDCR_EL2 ) : SailM
                                                  (BitVec 64) )
                                                (pure (((((_get_MDCR_EL2_Type_TDE w__79) +++ (_get_MDCR_EL2_Type_TDA
                                                        w__80)) != 0b00#2) : Bool)))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__82 : Bool)
                                      then
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                                      else
                                        (do
                                          let w__90 ← (( do
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
                                                     let w__86 ← (( do (HCR_read ()) ) : SailM
                                                       (BitVec 32) )
                                                     (pure ((((_get_HCR_Type_TGE w__86) == 1#1) : Bool)))) : Bool)
                                                then (pure true)
                                                else
                                                  (do
                                                    let w__87 ← (( do (HDCR_read ()) ) : SailM
                                                      (BitVec 32) )
                                                    let w__88 ← (( do (HDCR_read ()) ) : SailM
                                                      (BitVec 32) )
                                                    (pure (((((_get_HDCR_Type_TDE w__87) +++ (_get_HDCR_Type_TDA
                                                            w__88)) != 0b00#2) : Bool)))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__90 : Bool)
                                          then
                                            (do
                                              (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                                          else
                                            (do
                                              let w__94 ← (( do
                                                (pure ((← do
                                                      if ((← do
                                                           (HaveEL EL3)) : Bool)
                                                      then
                                                        (do
                                                          let w__92 ← (( do (ELUsingAArch32 EL3) )
                                                            : SailM Bool )
                                                          (pure (((! w__92) : Bool))))
                                                      else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__94 : Bool)
                                              then
                                                (do
                                                  let w__97 ← (( do
                                                    if ((← do
                                                         (Halted ())) : Bool)
                                                    then
                                                      (do
                                                        let w__96 ← (( do (EDSCR_read ()) ) :
                                                          SailM (BitVec 32) )
                                                        (pure ((((_get_EDSCR_Type_SDD w__96) == 1#1) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__97 : Bool)
                                                  then sailThrow ((Error_Undefined ()))
                                                  else
                                                    (do
                                                      (AArch64_AArch32SystemAccessTrap EL3
                                                        (BitVec.toNat 0x05#8))))
                                              else
                                                (do
                                                  let w__101 ← (( do
                                                    (pure ((← do
                                                          if ((← do
                                                               (HaveEL EL3)) : Bool)
                                                          then
                                                            (do
                                                              (ELUsingAArch32 EL3))
                                                          else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool)))
                                                    ) : SailM Bool )
                                                  if (w__101 : Bool)
                                                  then
                                                    (do
                                                      let w__104 ← (( do
                                                        if ((← do
                                                             (Halted ())) : Bool)
                                                        then
                                                          (do
                                                            let w__103 ← (( do (EDSCR_read ()) ) :
                                                              SailM (BitVec 32) )
                                                            (pure ((((_get_EDSCR_Type_SDD w__103) == 1#1) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__104 : Bool)
                                                      then sailThrow ((Error_Undefined ()))
                                                      else
                                                        (do
                                                          (AArch32_TakeMonitorTrapException ())))
                                                  else
                                                    (do
                                                      let w__108 ← (( do
                                                        (pure ((← do
                                                              if ((← do
                                                                   (HaveEL EL3)) : Bool)
                                                              then
                                                                (do
                                                                  let w__106 ← (( do
                                                                    (ELUsingAArch32 EL3) ) : SailM
                                                                    Bool )
                                                                  (pure (((! w__106) : Bool))))
                                                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool)))
                                                        ) : SailM Bool )
                                                      if (w__108 : Bool)
                                                      then
                                                        (do
                                                          let w__111 ← (( do
                                                            if ((← do
                                                                 (Halted ())) : Bool)
                                                            then
                                                              (do
                                                                let w__110 ← (( do (EDSCR_read ())
                                                                  ) : SailM (BitVec 32) )
                                                                (pure ((((_get_EDSCR_Type_SDD w__110) == 1#1) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__111 : Bool)
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
                                                              let w__112 ← (( do
                                                                (DBGDSCRint_read ()) ) : SailM
                                                                (BitVec 32) )
                                                              let split_vec :=
                                                                (Sail.BitVec.extractLsb w__112 31 28)
                                                              let w__113 ← (( do readReg PSTATE )
                                                                : SailM ProcState )
                                                              writeReg PSTATE { w__113 with N := (Sail.BitVec.extractLsb
                                                                  split_vec 3 3) }
                                                              let w__114 ← (( do readReg PSTATE )
                                                                : SailM ProcState )
                                                              writeReg PSTATE { w__114 with Z := (Sail.BitVec.extractLsb
                                                                  split_vec 2 2) }
                                                              let w__115 ← (( do readReg PSTATE )
                                                                : SailM ProcState )
                                                              writeReg PSTATE { w__115 with C := (Sail.BitVec.extractLsb
                                                                  split_vec 1 1) }
                                                              let w__116 ← (( do readReg PSTATE )
                                                                : SailM ProcState )
                                                              writeReg PSTATE { w__116 with V := (Sail.BitVec.extractLsb
                                                                  split_vec 0 0) })
                                                          else
                                                            (do
                                                              let w__117 ← (( do
                                                                (DBGDSCRint_read ()) ) : SailM
                                                                (BitVec 32) )
                                                              (R_set t (__get_DBGDSCRint w__117))))))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__127 ← (( do
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
                                    let w__121 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__121) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__125 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__125) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
              if (w__127 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__137 ← (( do
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
                                        let w__131 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__131) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL3))
                          else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__137 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__147 ← (( do
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
                                            let w__141 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__141) == 1#1) : Bool))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  let w__145 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__145) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__147 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__151 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__149 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                      (pure (((! w__149) : Bool))))
                                  else (pure false)) && ((__MDCR_EL2_TDCC == 1#1) : Bool))) ) :
                            SailM Bool )
                          if (w__151 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              let w__155 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HDCR_TDCC == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__155 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                              else
                                (do
                                  let w__161 ← (( do
                                    if ((← do
                                         if ((← do
                                              (EL2Enabled ())) : Bool)
                                         then
                                           (do
                                             let w__157 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                               Bool )
                                             (pure (((! w__157) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__159 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64)
                                          )
                                        let w__160 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64)
                                          )
                                        (pure (((((_get_MDCR_EL2_Type_TDE w__159) +++ (_get_MDCR_EL2_Type_TDA
                                                w__160)) != 0b00#2) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__161 : Bool)
                                  then
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                                  else
                                    (do
                                      let w__167 ← (( do
                                        if ((← do
                                             if ((← do
                                                  (EL2Enabled ())) : Bool)
                                             then
                                               (do
                                                 (ELUsingAArch32 EL2))
                                             else (pure false)) : Bool)
                                        then
                                          (do
                                            let w__165 ← (( do (HDCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            let w__166 ← (( do (HDCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure (((((_get_HDCR_Type_TDE w__165) +++ (_get_HDCR_Type_TDA
                                                    w__166)) != 0b00#2) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__167 : Bool)
                                      then
                                        (do
                                          (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                                      else
                                        (do
                                          let w__171 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       (HaveEL EL3)) : Bool)
                                                  then
                                                    (do
                                                      let w__169 ← (( do (ELUsingAArch32 EL3) ) :
                                                        SailM Bool )
                                                      (pure (((! w__169) : Bool))))
                                                  else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__171 : Bool)
                                          then
                                            (do
                                              let w__174 ← (( do
                                                if ((← do
                                                     (Halted ())) : Bool)
                                                then
                                                  (do
                                                    let w__173 ← (( do (EDSCR_read ()) ) : SailM
                                                      (BitVec 32) )
                                                    (pure ((((_get_EDSCR_Type_SDD w__173) == 1#1) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__174 : Bool)
                                              then sailThrow ((Error_Undefined ()))
                                              else
                                                (do
                                                  (AArch64_AArch32SystemAccessTrap EL3
                                                    (BitVec.toNat 0x05#8))))
                                          else
                                            (do
                                              let w__178 ← (( do
                                                (pure ((← do
                                                      if ((← do
                                                           (HaveEL EL3)) : Bool)
                                                      then
                                                        (do
                                                          (ELUsingAArch32 EL3))
                                                      else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__178 : Bool)
                                              then
                                                (do
                                                  let w__181 ← (( do
                                                    if ((← do
                                                         (Halted ())) : Bool)
                                                    then
                                                      (do
                                                        let w__180 ← (( do (EDSCR_read ()) ) :
                                                          SailM (BitVec 32) )
                                                        (pure ((((_get_EDSCR_Type_SDD w__180) == 1#1) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__181 : Bool)
                                                  then sailThrow ((Error_Undefined ()))
                                                  else
                                                    (do
                                                      (AArch32_TakeMonitorTrapException ())))
                                              else
                                                (do
                                                  let w__185 ← (( do
                                                    (pure ((← do
                                                          if ((← do
                                                               (HaveEL EL3)) : Bool)
                                                          then
                                                            (do
                                                              let w__183 ← (( do
                                                                (ELUsingAArch32 EL3) ) : SailM Bool
                                                                )
                                                              (pure (((! w__183) : Bool))))
                                                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool)))
                                                    ) : SailM Bool )
                                                  if (w__185 : Bool)
                                                  then
                                                    (do
                                                      let w__188 ← (( do
                                                        if ((← do
                                                             (Halted ())) : Bool)
                                                        then
                                                          (do
                                                            let w__187 ← (( do (EDSCR_read ()) ) :
                                                              SailM (BitVec 32) )
                                                            (pure ((((_get_EDSCR_Type_SDD w__187) == 1#1) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__188 : Bool)
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
                                                          let w__189 ← (( do (DBGDSCRint_read ())
                                                            ) : SailM (BitVec 32) )
                                                          let split_vec :=
                                                            (Sail.BitVec.extractLsb w__189 31 28)
                                                          let w__190 ← (( do readReg PSTATE ) :
                                                            SailM ProcState )
                                                          writeReg PSTATE { w__190 with N := (Sail.BitVec.extractLsb
                                                              split_vec 3 3) }
                                                          let w__191 ← (( do readReg PSTATE ) :
                                                            SailM ProcState )
                                                          writeReg PSTATE { w__191 with Z := (Sail.BitVec.extractLsb
                                                              split_vec 2 2) }
                                                          let w__192 ← (( do readReg PSTATE ) :
                                                            SailM ProcState )
                                                          writeReg PSTATE { w__192 with C := (Sail.BitVec.extractLsb
                                                              split_vec 1 1) }
                                                          let w__193 ← (( do readReg PSTATE ) :
                                                            SailM ProcState )
                                                          writeReg PSTATE { w__193 with V := (Sail.BitVec.extractLsb
                                                              split_vec 0 0) })
                                                      else
                                                        (do
                                                          let w__194 ← (( do (DBGDSCRint_read ())
                                                            ) : SailM (BitVec 32) )
                                                          (R_set t (__get_DBGDSCRint w__194))))))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__204 ← (( do
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
                                        let w__198 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__198) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__202 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__202) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__204 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__214 ← (( do
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
                                            let w__208 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__208) == 1#1) : Bool))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL3))
                              else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) : SailM Bool )
                      if (w__214 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__224 ← (( do
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
                                                let w__218 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__218) == 1#1) : Bool))))
                                            else (pure false)) : Bool)
                                       then
                                         (do
                                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                                       else (pure false)) : Bool)
                                  then
                                    (do
                                      let w__222 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__222) : Bool))))
                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__224 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              let w__228 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          let w__226 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__226) : Bool))))
                                      else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__228 : Bool)
                              then
                                (do
                                  let w__231 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__230 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__230) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__231 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                              else
                                (do
                                  let w__235 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (HaveEL EL3)) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL3))
                                          else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__235 : Bool)
                                  then
                                    (do
                                      let w__238 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__237 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__237) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__238 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch32_TakeMonitorTrapException ())))
                                  else
                                    (do
                                      let w__242 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (HaveEL EL3)) : Bool)
                                              then
                                                (do
                                                  let w__240 ← (( do (ELUsingAArch32 EL3) ) :
                                                    SailM Bool )
                                                  (pure (((! w__240) : Bool))))
                                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__242 : Bool)
                                      then
                                        (do
                                          let w__245 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__244 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__244) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__245 : Bool)
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
                                              let w__246 ← (( do (DBGDSCRint_read ()) ) : SailM
                                                (BitVec 32) )
                                              let split_vec := (Sail.BitVec.extractLsb w__246 31 28)
                                              let w__247 ← (( do readReg PSTATE ) : SailM
                                                ProcState )
                                              writeReg PSTATE { w__247 with N := (Sail.BitVec.extractLsb
                                                  split_vec 3 3) }
                                              let w__248 ← (( do readReg PSTATE ) : SailM
                                                ProcState )
                                              writeReg PSTATE { w__248 with Z := (Sail.BitVec.extractLsb
                                                  split_vec 2 2) }
                                              let w__249 ← (( do readReg PSTATE ) : SailM
                                                ProcState )
                                              writeReg PSTATE { w__249 with C := (Sail.BitVec.extractLsb
                                                  split_vec 1 1) }
                                              let w__250 ← (( do readReg PSTATE ) : SailM
                                                ProcState )
                                              writeReg PSTATE { w__250 with V := (Sail.BitVec.extractLsb
                                                  split_vec 0 0) })
                                          else
                                            (do
                                              let w__251 ← (( do (DBGDSCRint_read ()) ) : SailM
                                                (BitVec 32) )
                                              (R_set t (__get_DBGDSCRint w__251))))))))))
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
                              let w__252 ← (( do (DBGDSCRint_read ()) ) : SailM (BitVec 32) )
                              let split_vec := (Sail.BitVec.extractLsb w__252 31 28)
                              let w__253 ← (( do readReg PSTATE ) : SailM ProcState )
                              writeReg PSTATE { w__253 with N := (Sail.BitVec.extractLsb split_vec 3
                                  3) }
                              let w__254 ← (( do readReg PSTATE ) : SailM ProcState )
                              writeReg PSTATE { w__254 with Z := (Sail.BitVec.extractLsb split_vec 2
                                  2) }
                              let w__255 ← (( do readReg PSTATE ) : SailM ProcState )
                              writeReg PSTATE { w__255 with C := (Sail.BitVec.extractLsb split_vec 1
                                  1) }
                              let w__256 ← (( do readReg PSTATE ) : SailM ProcState )
                              writeReg PSTATE { w__256 with V := (Sail.BitVec.extractLsb split_vec 0
                                  0) })
                          else
                            (do
                              let w__257 ← (( do (DBGDSCRint_read ()) ) : SailM (BitVec 32) )
                              (R_set t (__get_DBGDSCRint w__257)))))
                  else (pure (()))))))


end ArmFull.Functions
