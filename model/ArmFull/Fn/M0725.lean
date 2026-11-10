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
import ArmFull.Fn.M0100
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
          let w__17 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
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
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8)))
                  else
                    (do
                      (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x0C#8))))
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
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8)))
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
                                (pure (((((_get_MDCR_EL2_Type_TDE w__41) +++ (_get_MDCR_EL2_Type_TDRA
                                        w__42)) != 0b00#2) : Bool)))))
                        else (pure false) ) : SailM Bool )
                      if (w__44 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8)))
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
                                    (pure (((((_get_HDCR_Type_TDE w__49) +++ (_get_HDCR_Type_TDRA
                                            w__50)) != 0b00#2) : Bool)))))
                            else (pure false) ) : SailM Bool )
                          if (w__52 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x0C#8)))
                          else
                            (do
                              let w__55 ← (( do
                                (pure ((← do
                                      if (((HaveEL EL3) : Bool) : Bool)
                                      then
                                        (do
                                          let w__53 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__53) : Bool))))
                                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__55 : Bool)
                              then
                                (do
                                  let w__58 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__57 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__57) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__58 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x0C#8))))
                              else
                                (do
                                  let w__59 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
                                  let w__60 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
                                  let (__tup_0, __tup_1) :=
                                    ((Sail.BitVec.extractLsb w__59 63 32), (Sail.BitVec.extractLsb
                                      w__60 31 0))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__69 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                then
                                  (do
                                    let w__63 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__63) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__67 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__67) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
              if (w__69 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__75 ← (( do
                    if ((← do
                         if ((← do
                              (EL2Enabled ())) : Bool)
                         then
                           (do
                             let w__71 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                             (pure (((! w__71) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__73 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        let w__74 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_MDCR_EL2_Type_TDE w__73) +++ (_get_MDCR_EL2_Type_TDRA w__74)) != 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__75 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8)))
                  else
                    (do
                      let w__81 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 (ELUsingAArch32 EL2))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__79 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                            let w__80 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                            (pure (((((_get_HDCR_Type_TDE w__79) +++ (_get_HDCR_Type_TDRA w__80)) != 0b00#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__81 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x0C#8)))
                      else
                        (do
                          let w__84 ← (( do
                            (pure ((← do
                                  if (((HaveEL EL3) : Bool) : Bool)
                                  then
                                    (do
                                      let w__82 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__82) : Bool))))
                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__84 : Bool)
                          then
                            (do
                              let w__87 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__86 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__86) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__87 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x0C#8))))
                          else
                            (do
                              let w__88 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
                              let w__89 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
                              let (__tup_0, __tup_1) :=
                                ((Sail.BitVec.extractLsb w__88 63 32), (Sail.BitVec.extractLsb w__89
                                  31 0))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__98 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         (pure ((← do
                                               (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                    then
                                      (do
                                        let w__92 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__92) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__96 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__96) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__98 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__101 ← (( do
                        (pure ((← do
                              if (((HaveEL EL3) : Bool) : Bool)
                              then
                                (do
                                  let w__99 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__99) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__101 : Bool)
                      then
                        (do
                          let w__104 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__103 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__103) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__104 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x0C#8))))
                      else
                        (do
                          let w__105 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
                          let w__106 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
                          let (__tup_0, __tup_1) :=
                            ((Sail.BitVec.extractLsb w__105 63 32), (Sail.BitVec.extractLsb w__106
                              31 0))
                          (R_set t2 __tup_0)
                          (R_set t __tup_1))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__107 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
                      let w__108 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) :=
                        ((Sail.BitVec.extractLsb w__107 63 32), (Sail.BitVec.extractLsb w__108 31 0))
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
          let w__17 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
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
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8)))
                  else
                    (do
                      (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x0C#8))))
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
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8)))
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
                                (pure (((((_get_MDCR_EL2_Type_TDE w__41) +++ (_get_MDCR_EL2_Type_TDRA
                                        w__42)) != 0b00#2) : Bool)))))
                        else (pure false) ) : SailM Bool )
                      if (w__44 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8)))
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
                                    (pure (((((_get_HDCR_Type_TDE w__49) +++ (_get_HDCR_Type_TDRA
                                            w__50)) != 0b00#2) : Bool)))))
                            else (pure false) ) : SailM Bool )
                          if (w__52 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x0C#8)))
                          else
                            (do
                              let w__55 ← (( do
                                (pure ((← do
                                      if (((HaveEL EL3) : Bool) : Bool)
                                      then
                                        (do
                                          let w__53 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__53) : Bool))))
                                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__55 : Bool)
                              then
                                (do
                                  let w__58 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__57 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__57) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__58 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x0C#8))))
                              else
                                (do
                                  let w__59 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
                                  let w__60 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
                                  let (__tup_0, __tup_1) :=
                                    ((Sail.BitVec.extractLsb w__59 63 32), (Sail.BitVec.extractLsb
                                      w__60 31 0))
                                  (R_set t2 __tup_0)
                                  (R_set t __tup_1))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__69 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                then
                                  (do
                                    let w__63 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__63) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__67 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__67) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
              if (w__69 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__75 ← (( do
                    if ((← do
                         if ((← do
                              (EL2Enabled ())) : Bool)
                         then
                           (do
                             let w__71 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                             (pure (((! w__71) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__73 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        let w__74 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_MDCR_EL2_Type_TDE w__73) +++ (_get_MDCR_EL2_Type_TDRA w__74)) != 0b00#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__75 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x0C#8)))
                  else
                    (do
                      let w__81 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 (ELUsingAArch32 EL2))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__79 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                            let w__80 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                            (pure (((((_get_HDCR_Type_TDE w__79) +++ (_get_HDCR_Type_TDRA w__80)) != 0b00#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__81 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x0C#8)))
                      else
                        (do
                          let w__84 ← (( do
                            (pure ((← do
                                  if (((HaveEL EL3) : Bool) : Bool)
                                  then
                                    (do
                                      let w__82 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__82) : Bool))))
                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__84 : Bool)
                          then
                            (do
                              let w__87 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__86 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__86) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__87 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x0C#8))))
                          else
                            (do
                              let w__88 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
                              let w__89 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
                              let (__tup_0, __tup_1) :=
                                ((Sail.BitVec.extractLsb w__88 63 32), (Sail.BitVec.extractLsb w__89
                                  31 0))
                              (R_set t2 __tup_0)
                              (R_set t __tup_1))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__98 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         (pure ((← do
                                               (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                                    then
                                      (do
                                        let w__92 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__92) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__96 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__96) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__98 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__101 ← (( do
                        (pure ((← do
                              if (((HaveEL EL3) : Bool) : Bool)
                              then
                                (do
                                  let w__99 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__99) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__101 : Bool)
                      then
                        (do
                          let w__104 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__103 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__103) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__104 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x0C#8))))
                      else
                        (do
                          let w__105 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
                          let w__106 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
                          let (__tup_0, __tup_1) :=
                            ((Sail.BitVec.extractLsb w__105 63 32), (Sail.BitVec.extractLsb w__106
                              31 0))
                          (R_set t2 __tup_0)
                          (R_set t __tup_1))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__107 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
                      let w__108 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) :=
                        ((Sail.BitVec.extractLsb w__107 63 32), (Sail.BitVec.extractLsb w__108 31 0))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1))
                  else (pure (()))))))


end ArmFull.Functions
