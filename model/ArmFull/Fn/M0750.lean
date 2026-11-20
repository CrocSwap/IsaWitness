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
public import ArmFull.Fn.M0054
public import ArmFull.Fn.M0100
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

/-- Type quantifiers: t : Int, t2 : Int -/
def DBGDRAR_SysRegRead64_89f87ddb7d53b509 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
      let w__8 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
      let (__tup_0, __tup_1) :=
        ((Sail.BitVec.extractLsb w__7 63 32), (Sail.BitVec.extractLsb w__8 31 0))
      (R_set t2 __tup_0)
      (R_set t __tup_1))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          let w__18 ← (( do
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
                                let w__12 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__12) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__16 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__16) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
          if (w__18 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__20 ← (( do
                (pure ((← do
                      let w__19 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                      (pure (((! w__19) : Bool)))) && ((__MDSCR_EL1_TDCC == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__20 : Bool)
              then
                (do
                  let w__25 ← (( do
                    if ((← do
                         if ((← do
                              (EL2Enabled ())) : Bool)
                         then
                           (do
                             let w__22 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                             (pure (((! w__22) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__24 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure ((((_get_HCR_EL2_Type_TGE w__24) == 1#1) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__25 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8)))
                  else
                    (do
                      (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x0C#8))))
              else
                (do
                  let w__27 ← (( do
                    (pure ((← do
                          (ELUsingAArch32 EL1)) && ((__DBGDSCRext_UDCCdis == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__27 : Bool)
                  then
                    (do
                      let w__32 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 let w__29 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                 (pure (((! w__29) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__31 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                            (pure ((((_get_HCR_EL2_Type_TGE w__31) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__32 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8)))
                      else
                        (do
                          let w__37 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     (ELUsingAArch32 EL2))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__36 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_HCR_Type_TGE w__36) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__37 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                          else sailThrow ((Error_Undefined ()))))
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
                                (pure (((((_get_MDCR_EL2_Type_TDE w__42) +++ (_get_MDCR_EL2_Type_TDRA
                                        w__43)) != 0b00#2) : Bool)))))
                        else (pure false) ) : SailM Bool )
                      if (w__45 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8)))
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
                                    (pure (((((_get_HDCR_Type_TDE w__50) +++ (_get_HDCR_Type_TDRA
                                            w__51)) != 0b00#2) : Bool)))))
                            else (pure false) ) : SailM Bool )
                          if (w__53 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x0C#8)))
                          else
                            (do
                              let w__57 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          let w__55 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__55) : Bool))))
                                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__57 : Bool)
                              then
                                (do
                                  let w__60 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__59 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__59) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__60 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x0C#8))))
                              else
                                (do
                                  let w__61 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
                                  let w__62 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
                                  let (__tup_0, __tup_1) :=
                                    ((Sail.BitVec.extractLsb w__61 63 32), (Sail.BitVec.extractLsb
                                      w__62 31 0))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__72 ← (( do
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
                                    let w__66 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__66) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__70 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__70) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
              if (w__72 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__78 ← (( do
                    if ((← do
                         if ((← do
                              (EL2Enabled ())) : Bool)
                         then
                           (do
                             let w__74 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                             (pure (((! w__74) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__76 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        let w__77 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_MDCR_EL2_Type_TDE w__76) +++ (_get_MDCR_EL2_Type_TDRA w__77)) != 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__78 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8)))
                  else
                    (do
                      let w__84 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 (ELUsingAArch32 EL2))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__82 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                            let w__83 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                            (pure (((((_get_HDCR_Type_TDE w__82) +++ (_get_HDCR_Type_TDRA w__83)) != 0b00#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__84 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x0C#8)))
                      else
                        (do
                          let w__88 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (HaveEL EL3)) : Bool)
                                  then
                                    (do
                                      let w__86 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__86) : Bool))))
                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__88 : Bool)
                          then
                            (do
                              let w__91 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__90 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__90) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__91 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x0C#8))))
                          else
                            (do
                              let w__92 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
                              let w__93 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
                              let (__tup_0, __tup_1) :=
                                ((Sail.BitVec.extractLsb w__92 63 32), (Sail.BitVec.extractLsb w__93
                                  31 0))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__103 ← (( do
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
                                        let w__97 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
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
                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__103 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__107 ← (( do
                        (pure ((← do
                              if ((← do
                                   (HaveEL EL3)) : Bool)
                              then
                                (do
                                  let w__105 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__105) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__107 : Bool)
                      then
                        (do
                          let w__110 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__109 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__109) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__110 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x0C#8))))
                      else
                        (do
                          let w__111 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
                          let w__112 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
                          let (__tup_0, __tup_1) :=
                            ((Sail.BitVec.extractLsb w__111 63 32), (Sail.BitVec.extractLsb w__112
                              31 0))
                          (R_set t2 __tup_0)
                          (R_set t __tup_1))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__113 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
                      let w__114 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) :=
                        ((Sail.BitVec.extractLsb w__113 63 32), (Sail.BitVec.extractLsb w__114 31 0))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def DBGDSAR_SysRegRead64_2f971e6eb001648b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
      let w__8 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
      let (__tup_0, __tup_1) :=
        ((Sail.BitVec.extractLsb w__7 63 32), (Sail.BitVec.extractLsb w__8 31 0))
      (R_set t2 __tup_0)
      (R_set t __tup_1))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          let w__18 ← (( do
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
                                let w__12 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__12) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__16 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__16) : Bool))))
                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
          if (w__18 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__20 ← (( do
                (pure ((← do
                      let w__19 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                      (pure (((! w__19) : Bool)))) && ((__MDSCR_EL1_TDCC == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__20 : Bool)
              then
                (do
                  let w__25 ← (( do
                    if ((← do
                         if ((← do
                              (EL2Enabled ())) : Bool)
                         then
                           (do
                             let w__22 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                             (pure (((! w__22) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__24 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure ((((_get_HCR_EL2_Type_TGE w__24) == 1#1) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__25 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8)))
                  else
                    (do
                      (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x0C#8))))
              else
                (do
                  let w__27 ← (( do
                    (pure ((← do
                          (ELUsingAArch32 EL1)) && ((__DBGDSCRext_UDCCdis == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__27 : Bool)
                  then
                    (do
                      let w__32 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 let w__29 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                 (pure (((! w__29) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__31 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                            (pure ((((_get_HCR_EL2_Type_TGE w__31) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__32 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8)))
                      else
                        (do
                          let w__37 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     (ELUsingAArch32 EL2))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__36 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_HCR_Type_TGE w__36) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__37 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                          else sailThrow ((Error_Undefined ()))))
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
                                (pure (((((_get_MDCR_EL2_Type_TDE w__42) +++ (_get_MDCR_EL2_Type_TDRA
                                        w__43)) != 0b00#2) : Bool)))))
                        else (pure false) ) : SailM Bool )
                      if (w__45 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8)))
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
                                    (pure (((((_get_HDCR_Type_TDE w__50) +++ (_get_HDCR_Type_TDRA
                                            w__51)) != 0b00#2) : Bool)))))
                            else (pure false) ) : SailM Bool )
                          if (w__53 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x0C#8)))
                          else
                            (do
                              let w__57 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          let w__55 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__55) : Bool))))
                                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__57 : Bool)
                              then
                                (do
                                  let w__60 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__59 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__59) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__60 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x0C#8))))
                              else
                                (do
                                  let w__61 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
                                  let w__62 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
                                  let (__tup_0, __tup_1) :=
                                    ((Sail.BitVec.extractLsb w__61 63 32), (Sail.BitVec.extractLsb
                                      w__62 31 0))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__72 ← (( do
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
                                    let w__66 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__66) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__70 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__70) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
              if (w__72 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__78 ← (( do
                    if ((← do
                         if ((← do
                              (EL2Enabled ())) : Bool)
                         then
                           (do
                             let w__74 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                             (pure (((! w__74) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__76 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        let w__77 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_MDCR_EL2_Type_TDE w__76) +++ (_get_MDCR_EL2_Type_TDRA w__77)) != 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__78 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8)))
                  else
                    (do
                      let w__84 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 (ELUsingAArch32 EL2))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__82 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                            let w__83 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                            (pure (((((_get_HDCR_Type_TDE w__82) +++ (_get_HDCR_Type_TDRA w__83)) != 0b00#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__84 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x0C#8)))
                      else
                        (do
                          let w__88 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (HaveEL EL3)) : Bool)
                                  then
                                    (do
                                      let w__86 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__86) : Bool))))
                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__88 : Bool)
                          then
                            (do
                              let w__91 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__90 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__90) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__91 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x0C#8))))
                          else
                            (do
                              let w__92 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
                              let w__93 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
                              let (__tup_0, __tup_1) :=
                                ((Sail.BitVec.extractLsb w__92 63 32), (Sail.BitVec.extractLsb w__93
                                  31 0))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__103 ← (( do
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
                                        let w__97 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
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
                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__103 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__107 ← (( do
                        (pure ((← do
                              if ((← do
                                   (HaveEL EL3)) : Bool)
                              then
                                (do
                                  let w__105 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__105) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__107 : Bool)
                      then
                        (do
                          let w__110 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__109 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__109) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__110 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x0C#8))))
                      else
                        (do
                          let w__111 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
                          let w__112 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
                          let (__tup_0, __tup_1) :=
                            ((Sail.BitVec.extractLsb w__111 63 32), (Sail.BitVec.extractLsb w__112
                              31 0))
                          (R_set t2 __tup_0)
                          (R_set t __tup_1))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__113 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
                      let w__114 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) :=
                        ((Sail.BitVec.extractLsb w__113 63 32), (Sail.BitVec.extractLsb w__114 31 0))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure (()))))))


end ArmFull.Functions
