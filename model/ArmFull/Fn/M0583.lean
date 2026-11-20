module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0011
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0073
public import ArmFull.Fn.M0075
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0183
public import ArmFull.Fn.M0188
public import ArmFull.Fn.M0252 set_option backward.proofsInPublic true @[expose] public section

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
def RCWMASK_EL1_SysRegRead128_7c7466f3a5148cfe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_RCWMASKEn : (BitVec 1) := (_get_SCR_EL3_Type_RCWMASKEn w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_D128En : (BitVec 1) := (_get_SCR_EL3_Type_D128En w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HFGRTR_EL2_nRCWMASK_EL1 : (BitVec 1) := (_get_HFGRTR_EL2_Type_nRCWMASK_EL1 w__5)
  let w__6 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_D128En : (BitVec 1) := (_get_HCRX_EL2_Type_D128En w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__13 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             if ((← do
                                  (Halted ())) : Bool)
                             then
                               (do
                                 (HaveEL EL3))
                             else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__SCR_EL3_RCWMASKEn == 0#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__20 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 if ((← do
                                      (Halted ())) : Bool)
                                 then
                                   (do
                                     (HaveEL EL3))
                                 else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
              if (w__20 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__27 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   (IsFeatureImplemented FEAT_FGT))
                               else (pure false)) : Bool)
                          then
                            (do
                              (pure ((← do
                                    let w__24 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__24) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HFGRTR_EL2_nRCWMASK_EL1 == 0#1) : Bool))) ) :
                    SailM Bool )
                  if (w__27 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      let w__31 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            (pure ((← do
                                  let w__29 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                                  (pure (((! w__29) : Bool)))) || ((__HCRX_EL2_D128En == 0#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__31 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                      else
                        (do
                          let w__33 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__SCR_EL3_RCWMASKEn == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__33 : Bool)
                          then
                            (do
                              let w__35 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__35 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                          else
                            (do
                              let w__37 ← (( do
                                (pure ((← do
                                      (HaveEL EL3)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) :
                                SailM Bool )
                              if (w__37 : Bool)
                              then
                                (do
                                  let w__39 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__39 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                              else
                                (do
                                  let w__40 ← (( do readReg RCWMASK_EL1 ) : SailM (BitVec 128) )
                                  let w__41 ← (( do readReg RCWMASK_EL1 ) : SailM (BitVec 128) )
                                  let (__tup_0, __tup_1) :=
                                    ((Sail.BitVec.extractLsb w__40 127 64), (Sail.BitVec.extractLsb
                                      w__41 63 0))
                                  (X_set (t +i 1) 64 __tup_0)
                                  (X_set t 64 __tup_1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__48 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 if ((← do
                                      (Halted ())) : Bool)
                                 then
                                   (do
                                     (HaveEL EL3))
                                 else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_RCWMASKEn == 0#1) : Bool))) ) : SailM Bool )
              if (w__48 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__55 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     if ((← do
                                          (Halted ())) : Bool)
                                     then
                                       (do
                                         (HaveEL EL3))
                                     else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__55 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__57 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_RCWMASKEn == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__57 : Bool)
                      then
                        (do
                          let w__59 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__59 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                      else
                        (do
                          let w__61 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__61 : Bool)
                          then
                            (do
                              let w__63 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__63 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                          else
                            (do
                              let w__64 ← (( do readReg RCWMASK_EL1 ) : SailM (BitVec 128) )
                              let w__65 ← (( do readReg RCWMASK_EL1 ) : SailM (BitVec 128) )
                              let (__tup_0, __tup_1) :=
                                ((Sail.BitVec.extractLsb w__64 127 64), (Sail.BitVec.extractLsb
                                  w__65 63 0))
                              (X_set (t +i 1) 64 __tup_0)
                              (X_set t 64 __tup_1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__66 ← (( do readReg RCWMASK_EL1 ) : SailM (BitVec 128) )
                  let w__67 ← (( do readReg RCWMASK_EL1 ) : SailM (BitVec 128) )
                  let (__tup_0, __tup_1) :=
                    ((Sail.BitVec.extractLsb w__66 127 64), (Sail.BitVec.extractLsb w__67 63 0))
                  (X_set (t +i 1) 64 __tup_0)
                  (X_set t 64 __tup_1))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def RCWSMASK_EL1_SysRegRead128_7cac5e35b1fae5f9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_RCWMASKEn : (BitVec 1) := (_get_SCR_EL3_Type_RCWMASKEn w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_D128En : (BitVec 1) := (_get_SCR_EL3_Type_D128En w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn2 : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn2 w__4)
  let w__5 ← (( do readReg HFGRTR2_EL2 ) : SailM (BitVec 64) )
  let __HFGRTR2_EL2_nRCWSMASK_EL1 : (BitVec 1) := (_get_HFGRTR2_EL2_Type_nRCWSMASK_EL1 w__5)
  let w__6 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_D128En : (BitVec 1) := (_get_HCRX_EL2_Type_D128En w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__13 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             if ((← do
                                  (Halted ())) : Bool)
                             then
                               (do
                                 (HaveEL EL3))
                             else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__SCR_EL3_RCWMASKEn == 0#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__20 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 if ((← do
                                      (Halted ())) : Bool)
                                 then
                                   (do
                                     (HaveEL EL3))
                                 else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
              if (w__20 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__26 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   (IsFeatureImplemented FEAT_FGT2))
                               else (pure false)) : Bool)
                          then
                            (do
                              (HaveEL EL3))
                          else (pure false)) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__26 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      let w__30 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (IsFeatureImplemented FEAT_FGT2))
                              else (pure false)) && ((__HFGRTR2_EL2_nRCWSMASK_EL1 == 0#1) : Bool)))
                        ) : SailM Bool )
                      if (w__30 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                      else
                        (do
                          let w__34 ← (( do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (pure ((← do
                                      let w__32 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                                      (pure (((! w__32) : Bool)))) || ((__HCRX_EL2_D128En == 0#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__34 : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                          else
                            (do
                              let w__36 ← (( do
                                (pure ((← do
                                      (HaveEL EL3)) && ((__SCR_EL3_RCWMASKEn == 0#1) : Bool))) ) :
                                SailM Bool )
                              if (w__36 : Bool)
                              then
                                (do
                                  let w__38 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__38 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                              else
                                (do
                                  let w__40 ← (( do
                                    (pure ((← do
                                          (HaveEL EL3)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__40 : Bool)
                                  then
                                    (do
                                      let w__42 ← (( do
                                        (pure ((← do
                                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) :
                                        SailM Bool )
                                      if (w__42 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                                  else
                                    (do
                                      let w__43 ← (( do readReg RCWSMASK_EL1 ) : SailM
                                        (BitVec 128) )
                                      let w__44 ← (( do readReg RCWSMASK_EL1 ) : SailM
                                        (BitVec 128) )
                                      let (__tup_0, __tup_1) :=
                                        ((Sail.BitVec.extractLsb w__43 127 64), (Sail.BitVec.extractLsb
                                          w__44 63 0))
                                      (X_set (t +i 1) 64 __tup_0)
                                      (X_set t 64 __tup_1)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__51 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 if ((← do
                                      (Halted ())) : Bool)
                                 then
                                   (do
                                     (HaveEL EL3))
                                 else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_RCWMASKEn == 0#1) : Bool))) ) : SailM Bool )
              if (w__51 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__58 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     if ((← do
                                          (Halted ())) : Bool)
                                     then
                                       (do
                                         (HaveEL EL3))
                                     else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__58 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__60 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_RCWMASKEn == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__60 : Bool)
                      then
                        (do
                          let w__62 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__62 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                      else
                        (do
                          let w__64 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__64 : Bool)
                          then
                            (do
                              let w__66 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__66 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                          else
                            (do
                              let w__67 ← (( do readReg RCWSMASK_EL1 ) : SailM (BitVec 128) )
                              let w__68 ← (( do readReg RCWSMASK_EL1 ) : SailM (BitVec 128) )
                              let (__tup_0, __tup_1) :=
                                ((Sail.BitVec.extractLsb w__67 127 64), (Sail.BitVec.extractLsb
                                  w__68 63 0))
                              (X_set (t +i 1) 64 __tup_0)
                              (X_set t 64 __tup_1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__69 ← (( do readReg RCWSMASK_EL1 ) : SailM (BitVec 128) )
                  let w__70 ← (( do readReg RCWSMASK_EL1 ) : SailM (BitVec 128) )
                  let (__tup_0, __tup_1) :=
                    ((Sail.BitVec.extractLsb w__69 127 64), (Sail.BitVec.extractLsb w__70 63 0))
                  (X_set (t +i 1) 64 __tup_0)
                  (X_set t 64 __tup_1))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def S3_op1_Cn_Cm_op2_SysRegRead128_6403c05d5d1898d5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_EnIDCP128 : (BitVec 1) := (_get_SCR_EL3_Type_EnIDCP128 w__2)
  let w__3 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_TIDCP : (BitVec 1) := (_get_SCTLR_EL1_Type_TIDCP w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__4)
  let w__5 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let __SCTLR_EL2_TIDCP : (BitVec 1) := (_get_SCTLR_EL2_Type_TIDCP w__5)
  let w__6 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
  let __SCTLR2_EL1_EnIDCP128 : (BitVec 1) := (_get_SCTLR2_EL1_Type_EnIDCP128 w__6)
  let w__7 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
  let __SCTLR2_EL2_EnIDCP128 : (BitVec 1) := (_get_SCTLR2_EL2_Type_EnIDCP128 w__7)
  let w__8 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_EnIDCP128 : (BitVec 1) := (_get_HCRX_EL2_Type_EnIDCP128 w__8)
  let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TIDCP : (BitVec 1) := (_get_HCR_EL2_Type_TIDCP w__9)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__16 ← (( do
        (pure ((← do
              if ((← do
                   (pure ((← do
                         if ((← do
                              (Halted ())) : Bool)
                         then
                           (do
                             (HaveEL EL3))
                         else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
              then
                (do
                  (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
              else (pure false)) && ((__SCR_EL3_EnIDCP128 == 0#1) : Bool))) ) : SailM Bool )
      if (w__16 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__21 ← (( do
            (pure ((← do
                  let w__20 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__19 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_E2H w__18) +++ (_get_HCR_EL2_Type_TGE w__19)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  (pure (((! w__20) : Bool)))) && ((__SCTLR_EL1_TIDCP == 1#1) : Bool))) ) : SailM
            Bool )
          if (w__21 : Bool)
          then
            (do
              let w__23 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__23 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x14#8))))
          else
            (do
              let w__28 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__25 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__25) +++ (_get_HCR_EL2_Type_TGE w__26)) == 0b11#2) : Bool))))
                      else (pure false)) && ((__SCTLR_EL2_TIDCP == 1#1) : Bool))) ) : SailM Bool )
              if (w__28 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else
                (do
                  let w__35 ← (( do
                    if ((← do
                         let w__32 ← (( do
                           if ((← do
                                (EL2Enabled ())) : Bool)
                           then
                             (do
                               let w__30 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                               let w__31 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                               (pure (((((_get_HCR_EL2_Type_E2H w__30) +++ (_get_HCR_EL2_Type_TGE
                                       w__31)) == 0b11#2) : Bool))))
                           else (pure false) ) : SailM Bool )
                         (pure (((! w__32) : Bool)))) : Bool)
                    then
                      (do
                        (pure ((← do
                              let w__33 ← (( do (IsSCTLR2EL1Enabled ()) ) : SailM Bool )
                              (pure (((! w__33) : Bool)))) || ((__SCTLR2_EL1_EnIDCP128 == 0#1) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__35 : Bool)
                  then
                    (do
                      let w__37 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                      if (w__37 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x14#8))))
                  else
                    (do
                      let w__44 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 let w__39 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 let w__40 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 (pure (((((_get_HCR_EL2_Type_E2H w__39) +++ (_get_HCR_EL2_Type_TGE
                                         w__40)) == 0b11#2) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            (pure ((← do
                                  let w__42 ← (( do (IsSCTLR2EL2Enabled ()) ) : SailM Bool )
                                  (pure (((! w__42) : Bool)))) || ((__SCTLR2_EL2_EnIDCP128 == 0#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__44 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                      else
                        (do
                          let w__51 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     let w__46 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     let w__47 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     (pure (((((_get_HCR_EL2_Type_E2H w__46) +++ (_get_HCR_EL2_Type_TGE
                                             w__47)) != 0b11#2) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                (pure ((← do
                                      let w__49 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                                      (pure (((! w__49) : Bool)))) || ((__HCRX_EL2_EnIDCP128 == 0#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__51 : Bool)
                          then
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                          else
                            (do
                              let w__53 ← (( do
                                (pure ((← do
                                      (HaveEL EL3)) && ((__SCR_EL3_EnIDCP128 == 0#1) : Bool))) ) :
                                SailM Bool )
                              if (w__53 : Bool)
                              then
                                (do
                                  let w__55 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__55 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                              else
                                (do
                                  (AArch64_ImpDefSysRegRead128 op0 op1 CRn CRm op2 t (t +i 1))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__62 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             if ((← do
                                  (Halted ())) : Bool)
                             then
                               (do
                                 (HaveEL EL3))
                             else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__SCR_EL3_EnIDCP128 == 0#1) : Bool))) ) : SailM Bool )
          if (w__62 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__64 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TIDCP == 1#1) : Bool))) ) : SailM Bool )
              if (w__64 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else
                (do
                  let w__68 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        (pure ((← do
                              let w__66 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                              (pure (((! w__66) : Bool)))) || ((__HCRX_EL2_EnIDCP128 == 0#1) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__68 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      let w__70 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_EnIDCP128 == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__70 : Bool)
                      then
                        (do
                          let w__72 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__72 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                      else
                        (do
                          (AArch64_ImpDefSysRegRead128 op0 op1 CRn CRm op2 t (t +i 1)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__79 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 if ((← do
                                      (Halted ())) : Bool)
                                 then
                                   (do
                                     (HaveEL EL3))
                                 else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_EnIDCP128 == 0#1) : Bool))) ) : SailM Bool )
              if (w__79 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__81 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__SCR_EL3_EnIDCP128 == 0#1) : Bool))) ) : SailM Bool )
                  if (w__81 : Bool)
                  then
                    (do
                      let w__83 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__83 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                  else
                    (do
                      (AArch64_ImpDefSysRegRead128 op0 op1 CRn CRm op2 t (t +i 1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  (AArch64_ImpDefSysRegRead128 op0 op1 CRn CRm op2 t (t +i 1)))
              else (pure (())))))


end ArmFull.Functions
