module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0082
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0149
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
              let w__20 ← (( do
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
                                    let w__14 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__14) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__18 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__18) : Bool))))
                      else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
              if (w__20 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__30 ← (( do
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
                                        let w__24 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__24) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL3))
                          else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__30 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__40 ← (( do
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
                                            let w__34 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__34) == 1#1) : Bool))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  let w__38 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__38) : Bool))))
                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__40 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__44 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__42 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                      (pure (((! w__42) : Bool))))
                                  else (pure false)) && ((__MDCR_EL2_TDCC == 1#1) : Bool))) ) :
                            SailM Bool )
                          if (w__44 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              let w__48 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HDCR_TDCC == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__48 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                              else
                                (do
                                  let w__54 ← (( do
                                    if ((← do
                                         if ((← do
                                              (EL2Enabled ())) : Bool)
                                         then
                                           (do
                                             let w__50 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool
                                               )
                                             (pure (((! w__50) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__52 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                                        let w__53 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                                        (pure (((((_get_MDCR_EL2_Type_TDE w__52) +++ (_get_MDCR_EL2_Type_TDA
                                                w__53)) != 0b00#2) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__54 : Bool)
                                  then
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8)))
                                  else
                                    (do
                                      let w__60 ← (( do
                                        if ((← do
                                             if ((← do
                                                  (EL2Enabled ())) : Bool)
                                             then
                                               (do
                                                 (ELUsingAArch32 EL2))
                                             else (pure false)) : Bool)
                                        then
                                          (do
                                            let w__58 ← (( do (HDCR_read ()) ) : SailM (BitVec 32)
                                              )
                                            let w__59 ← (( do (HDCR_read ()) ) : SailM (BitVec 32)
                                              )
                                            (pure (((((_get_HDCR_Type_TDE w__58) +++ (_get_HDCR_Type_TDA
                                                    w__59)) != 0b00#2) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__60 : Bool)
                                      then
                                        (do
                                          (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8)))
                                      else
                                        (do
                                          let w__64 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       (HaveEL EL3)) : Bool)
                                                  then
                                                    (do
                                                      let w__62 ← (( do (ELUsingAArch32 EL3) ) :
                                                        SailM Bool )
                                                      (pure (((! w__62) : Bool))))
                                                  else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__64 : Bool)
                                          then
                                            (do
                                              let w__67 ← (( do
                                                if ((← do
                                                     (Halted ())) : Bool)
                                                then
                                                  (do
                                                    let w__66 ← (( do (EDSCR_read ()) ) : SailM
                                                      (BitVec 32) )
                                                    (pure ((((_get_EDSCR_Type_SDD w__66) == 1#1) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__67 : Bool)
                                              then sailThrow ((Error_Undefined ()))
                                              else
                                                (do
                                                  (AArch64_AArch32SystemAccessTrap EL3
                                                    (BitVec.toNat 0x05#8))))
                                          else
                                            (do
                                              let w__71 ← (( do
                                                (pure ((← do
                                                      if ((← do
                                                           (HaveEL EL3)) : Bool)
                                                      then
                                                        (do
                                                          (ELUsingAArch32 EL3))
                                                      else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool)))
                                                ) : SailM Bool )
                                              if (w__71 : Bool)
                                              then
                                                (do
                                                  let w__74 ← (( do
                                                    if ((← do
                                                         (Halted ())) : Bool)
                                                    then
                                                      (do
                                                        let w__73 ← (( do (EDSCR_read ()) ) :
                                                          SailM (BitVec 32) )
                                                        (pure ((((_get_EDSCR_Type_SDD w__73) == 1#1) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__74 : Bool)
                                                  then sailThrow ((Error_Undefined ()))
                                                  else
                                                    (do
                                                      (AArch32_TakeMonitorTrapException ())))
                                              else
                                                (do
                                                  let w__78 ← (( do
                                                    (pure ((← do
                                                          if ((← do
                                                               (HaveEL EL3)) : Bool)
                                                          then
                                                            (do
                                                              let w__76 ← (( do
                                                                (ELUsingAArch32 EL3) ) : SailM Bool
                                                                )
                                                              (pure (((! w__76) : Bool))))
                                                          else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool)))
                                                    ) : SailM Bool )
                                                  if (w__78 : Bool)
                                                  then
                                                    (do
                                                      let w__81 ← (( do
                                                        if ((← do
                                                             (Halted ())) : Bool)
                                                        then
                                                          (do
                                                            let w__80 ← (( do (EDSCR_read ()) ) :
                                                              SailM (BitVec 32) )
                                                            (pure ((((_get_EDSCR_Type_SDD w__80) == 1#1) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__81 : Bool)
                                                      then sailThrow ((Error_Undefined ()))
                                                      else
                                                        (do
                                                          (AArch64_AArch32SystemAccessTrap EL3
                                                            (BitVec.toNat 0x05#8))))
                                                  else
                                                    (do
                                                      let w__82 ← (( do (DBGDTRTXext_read ()) ) :
                                                        SailM (BitVec 32) )
                                                      (R_set t w__82))))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__92 ← (( do
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
                                        let w__86 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__86) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__90 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__90) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__92 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__102 ← (( do
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
                                            let w__96 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__96) == 1#1) : Bool))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL3))
                              else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) : SailM Bool )
                      if (w__102 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__112 ← (( do
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
                                                let w__106 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__106) == 1#1) : Bool))))
                                            else (pure false)) : Bool)
                                       then
                                         (do
                                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                                       else (pure false)) : Bool)
                                  then
                                    (do
                                      let w__110 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__110) : Bool))))
                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__112 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              let w__116 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          let w__114 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__114) : Bool))))
                                      else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__116 : Bool)
                              then
                                (do
                                  let w__119 ← (( do
                                    if ((← do
                                         (Halted ())) : Bool)
                                    then
                                      (do
                                        let w__118 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__118) == 1#1) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__119 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                              else
                                (do
                                  let w__123 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (HaveEL EL3)) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL3))
                                          else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__123 : Bool)
                                  then
                                    (do
                                      let w__126 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__125 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__125) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__126 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch32_TakeMonitorTrapException ())))
                                  else
                                    (do
                                      let w__130 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (HaveEL EL3)) : Bool)
                                              then
                                                (do
                                                  let w__128 ← (( do (ELUsingAArch32 EL3) ) :
                                                    SailM Bool )
                                                  (pure (((! w__128) : Bool))))
                                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__130 : Bool)
                                      then
                                        (do
                                          let w__133 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__132 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__132) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__133 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x05#8))))
                                      else
                                        (do
                                          let w__134 ← (( do (DBGDTRTXext_read ()) ) : SailM
                                            (BitVec 32) )
                                          (R_set t w__134))))))))
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
                          let w__135 ← (( do (DBGDTRTXext_read ()) ) : SailM (BitVec 32) )
                          (R_set t w__135)))
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
                          let w__50 ← (( do (DBGOSDLR_read ()) ) : SailM (BitVec 32) )
                          let w__51 ← (( do (__get_DBGOSDLR w__50) ) : SailM (BitVec 32) )
                          (R_set t w__51))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__66 ← (( do
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
                                        let w__55 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__55) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__59 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__59) : Bool))))
                          else (pure false)) : Bool)
                     then
                       (do
                         let w__61 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                         (pure ((((_get_MDCR_EL3_Type_TDOSA w__61) == 1#1) : Bool))))
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
              if (w__66 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__75 ← (( do
                    if ((← do
                         if ((← do
                              if ((← do
                                   (HaveEL EL3)) : Bool)
                              then
                                (do
                                  let w__68 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__68) : Bool))))
                              else (pure false)) : Bool)
                         then
                           (do
                             let w__70 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                             (pure ((((_get_MDCR_EL3_Type_TDOSA w__70) == 1#1) : Bool))))
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
                  if (w__75 : Bool)
                  then
                    (do
                      let w__78 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__77 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__77) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__78 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8))))
                  else
                    (do
                      let w__79 ← (( do (DBGOSDLR_read ()) ) : SailM (BitVec 32) )
                      let w__80 ← (( do (__get_DBGOSDLR w__79) ) : SailM (BitVec 32) )
                      (R_set t w__80))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__81 ← (( do (DBGOSDLR_read ()) ) : SailM (BitVec 32) )
                  let w__82 ← (( do (__get_DBGOSDLR w__81) ) : SailM (BitVec 32) )
                  (R_set t w__82))
              else (pure (())))))


end ArmFull.Functions
