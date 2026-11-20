module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0058
public import ArmFull.Fn.M0072
public import ArmFull.Fn.M0073
public import ArmFull.Fn.M0075
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0183
public import ArmFull.Fn.M0208
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
def TTBR0_EL2_SysRegRead128_05dc18b820cc86b7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_D128En : (BitVec 1) := (_get_SCR_EL3_Type_D128En w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__12 ← (( do
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
              if (w__12 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__14 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
                  if (w__14 : Bool)
                  then
                    (do
                      let w__16 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__16 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                  else
                    (do
                      let w__17 ← (( do (TTBR0_EL2_read ()) ) : SailM (BitVec 128) )
                      let (__tup_0, __tup_1) ← (( do (Split w__17 64) ) : SailM
                        ((BitVec 64) × (BitVec 64)) )
                      (X_set (t +i 1) 64 __tup_0)
                      (X_set t 64 __tup_1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__18 ← (( do (TTBR0_EL2_read ()) ) : SailM (BitVec 128) )
                  let (__tup_0, __tup_1) ← (( do (Split w__18 64) ) : SailM
                    ((BitVec 64) × (BitVec 64)) )
                  (X_set (t +i 1) 64 __tup_0)
                  (X_set t 64 __tup_1))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR1_EL2_SysRegRead128_712360e50061655a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_D128En : (BitVec 1) := (_get_SCR_EL3_Type_D128En w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__12 ← (( do
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
              if (w__12 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__14 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
                  if (w__14 : Bool)
                  then
                    (do
                      let w__16 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__16 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                  else
                    (do
                      let w__17 ← (( do readReg TTBR1_EL2 ) : SailM (BitVec 128) )
                      let (__tup_0, __tup_1) ← (( do (Split w__17 64) ) : SailM
                        ((BitVec 64) × (BitVec 64)) )
                      (X_set (t +i 1) 64 __tup_0)
                      (X_set t 64 __tup_1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__18 ← (( do readReg TTBR1_EL2 ) : SailM (BitVec 128) )
                  let (__tup_0, __tup_1) ← (( do (Split w__18 64) ) : SailM
                    ((BitVec 64) × (BitVec 64)) )
                  (X_set (t +i 1) 64 __tup_0)
                  (X_set t 64 __tup_1))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def PAR_EL1_SysRegWrite128_e67f3244d494abe6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_D128En : (BitVec 1) := (_get_SCR_EL3_Type_D128En w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR_EL2_PAR_EL1 : (BitVec 1) := (_get_HFGWTR_EL2_Type_PAR_EL1 w__4)
  let w__5 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_D128En : (BitVec 1) := (_get_HCRX_EL2_Type_D128En w__5)
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
          if (w__12 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__19 ← (( do
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
                                let w__16 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__16) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGWTR_EL2_PAR_EL1 == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__19 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else
                (do
                  let w__23 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        (pure ((← do
                              let w__21 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                              (pure (((! w__21) : Bool)))) || ((__HCRX_EL2_D128En == 0#1) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__23 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      let w__25 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
                      if (w__25 : Bool)
                      then
                        (do
                          let w__27 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__27 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                      else
                        (do
                          let w__28 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                          let w__29 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          let (__tup_0, __tup_1) := (w__28, w__29)
                          let w__30 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                          (PAR_EL1_write
                            (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange w__30 127 64 __tup_0)))
                          let w__31 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                          (PAR_EL1_write
                            (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange w__31 63 0 __tup_1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__38 ← (( do
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
              if (w__38 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__40 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
                  if (w__40 : Bool)
                  then
                    (do
                      let w__42 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__42 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                  else
                    (do
                      let w__43 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                      let w__44 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) := (w__43, w__44)
                      let w__45 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                      (PAR_EL1_write
                        (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange w__45 127 64 __tup_0)))
                      let w__46 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                      (PAR_EL1_write
                        (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange w__46 63 0 __tup_1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__47 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                  let w__48 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  let (__tup_0, __tup_1) := (w__47, w__48)
                  let w__49 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                  (PAR_EL1_write (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange w__49 127 64 __tup_0)))
                  let w__50 ← (( do (PAR_EL1_read ()) ) : SailM (BitVec 128) )
                  (PAR_EL1_write (Mk_PAR_EL1_Type (Sail.BitVec.updateSubrange w__50 63 0 __tup_1))))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def RCWMASK_EL1_SysRegWrite128_b8a59eaf95f35a5f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
  let w__5 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR_EL2_nRCWMASK_EL1 : (BitVec 1) := (_get_HFGWTR_EL2_Type_nRCWMASK_EL1 w__5)
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
                          else (pure false)) && ((__HFGWTR_EL2_nRCWMASK_EL1 == 0#1) : Bool))) ) :
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
                                  let w__40 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                                  let w__41 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  let (tup__0, tup__1) :=
                                    ((w__40, w__41) : ((BitVec 64) × (BitVec 64)))
                                  let w__42 ← (( do readReg RCWMASK_EL1 ) : SailM (BitVec 128) )
                                  writeReg RCWMASK_EL1 (Sail.BitVec.updateSubrange w__42 127 64
                                    tup__0)
                                  let w__43 ← (( do readReg RCWMASK_EL1 ) : SailM (BitVec 128) )
                                  writeReg RCWMASK_EL1 (Sail.BitVec.updateSubrange w__43 63 0 tup__1))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__50 ← (( do
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
              if (w__50 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__57 ← (( do
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
                  if (w__57 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__59 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_RCWMASKEn == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__59 : Bool)
                      then
                        (do
                          let w__61 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__61 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                      else
                        (do
                          let w__63 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__63 : Bool)
                          then
                            (do
                              let w__65 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__65 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                          else
                            (do
                              let w__66 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                              let w__67 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              let (tup__0, tup__1) :=
                                ((w__66, w__67) : ((BitVec 64) × (BitVec 64)))
                              let w__68 ← (( do readReg RCWMASK_EL1 ) : SailM (BitVec 128) )
                              writeReg RCWMASK_EL1 (Sail.BitVec.updateSubrange w__68 127 64 tup__0)
                              let w__69 ← (( do readReg RCWMASK_EL1 ) : SailM (BitVec 128) )
                              writeReg RCWMASK_EL1 (Sail.BitVec.updateSubrange w__69 63 0 tup__1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__70 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                  let w__71 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  let (tup__0, tup__1) := ((w__70, w__71) : ((BitVec 64) × (BitVec 64)))
                  let w__72 ← (( do readReg RCWMASK_EL1 ) : SailM (BitVec 128) )
                  writeReg RCWMASK_EL1 (Sail.BitVec.updateSubrange w__72 127 64 tup__0)
                  let w__73 ← (( do readReg RCWMASK_EL1 ) : SailM (BitVec 128) )
                  writeReg RCWMASK_EL1 (Sail.BitVec.updateSubrange w__73 63 0 tup__1))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def RCWSMASK_EL1_SysRegWrite128_d70b97b0479af313 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
  let w__5 ← (( do readReg HFGWTR2_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR2_EL2_nRCWSMASK_EL1 : (BitVec 1) := (_get_HFGWTR2_EL2_Type_nRCWSMASK_EL1 w__5)
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
                              else (pure false)) && ((__HFGWTR2_EL2_nRCWSMASK_EL1 == 0#1) : Bool)))
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
                                      let w__43 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64)
                                        )
                                      let w__44 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      let (tup__0, tup__1) :=
                                        ((w__43, w__44) : ((BitVec 64) × (BitVec 64)))
                                      let w__45 ← (( do readReg RCWSMASK_EL1 ) : SailM
                                        (BitVec 128) )
                                      writeReg RCWSMASK_EL1 (Sail.BitVec.updateSubrange w__45 127 64
                                        tup__0)
                                      let w__46 ← (( do readReg RCWSMASK_EL1 ) : SailM
                                        (BitVec 128) )
                                      writeReg RCWSMASK_EL1 (Sail.BitVec.updateSubrange w__46 63 0
                                        tup__1)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__53 ← (( do
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
              if (w__53 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__60 ← (( do
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
                  if (w__60 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__62 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_RCWMASKEn == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__62 : Bool)
                      then
                        (do
                          let w__64 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__64 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                      else
                        (do
                          let w__66 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__66 : Bool)
                          then
                            (do
                              let w__68 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__68 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                          else
                            (do
                              let w__69 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                              let w__70 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              let (tup__0, tup__1) :=
                                ((w__69, w__70) : ((BitVec 64) × (BitVec 64)))
                              let w__71 ← (( do readReg RCWSMASK_EL1 ) : SailM (BitVec 128) )
                              writeReg RCWSMASK_EL1 (Sail.BitVec.updateSubrange w__71 127 64 tup__0)
                              let w__72 ← (( do readReg RCWSMASK_EL1 ) : SailM (BitVec 128) )
                              writeReg RCWSMASK_EL1 (Sail.BitVec.updateSubrange w__72 63 0 tup__1))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__73 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                  let w__74 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  let (tup__0, tup__1) := ((w__73, w__74) : ((BitVec 64) × (BitVec 64)))
                  let w__75 ← (( do readReg RCWSMASK_EL1 ) : SailM (BitVec 128) )
                  writeReg RCWSMASK_EL1 (Sail.BitVec.updateSubrange w__75 127 64 tup__0)
                  let w__76 ← (( do readReg RCWSMASK_EL1 ) : SailM (BitVec 128) )
                  writeReg RCWSMASK_EL1 (Sail.BitVec.updateSubrange w__76 63 0 tup__1))
              else (pure (())))))


end ArmFull.Functions
