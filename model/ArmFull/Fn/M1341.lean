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
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0058
public import ArmFull.Fn.M0073
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0183
public import ArmFull.Fn.M0202
public import ArmFull.Fn.M0208
public import ArmFull.Fn.M0252
public import ArmFull.Fn.M1235 set_option backward.proofsInPublic true @[expose] public section

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
def TTBR1_EL2_SysRegRead128_ae708511fcb38e92 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_D128En : (BitVec 1) := (_get_SCR_EL3_Type_D128En w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TRVM : (BitVec 1) := (_get_HCR_EL2_Type_TRVM w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HFGRTR_EL2_TTBR1_EL1 : (BitVec 1) := (_get_HFGRTR_EL2_Type_TTBR1_EL1 w__5)
  let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__6)
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
                  else (pure false)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__15 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TRVM == 1#1) : Bool))) ) : SailM Bool )
              if (w__15 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else
                (do
                  let w__22 ← (( do
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
                                    let w__19 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__19) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HFGRTR_EL2_TTBR1_EL1 == 1#1) : Bool))) ) : SailM
                    Bool )
                  if (w__22 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      let w__24 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
                      if (w__24 : Bool)
                      then
                        (do
                          let w__26 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__26 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                      else
                        (do
                          let w__31 ← (( do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                let w__29 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                let w__30 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                (pure (((((_get_HCR_EL2_Type_NV2 w__28) +++ ((_get_HCR_EL2_Type_NV1
                                          w__29) +++ (_get_HCR_EL2_Type_NV w__30))) == 0b111#3) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__31 : Bool)
                          then
                            (do
                              let w__32 ← (( do (NVMem_read__1 (BitVec.toNat 0x210#12) 128) ) :
                                SailM (BitVec 128) )
                              let (__tup_0, __tup_1) ← (( do (Split w__32 64) ) : SailM
                                ((BitVec 64) × (BitVec 64)) )
                              (X_set (t +i 1) 64 __tup_0)
                              (X_set t 64 __tup_1))
                          else
                            (do
                              let w__33 ← (( do (TTBR1_EL1_read ()) ) : SailM (BitVec 128) )
                              let (__tup_0, __tup_1) ← (( do (Split w__33 64) ) : SailM
                                ((BitVec 64) × (BitVec 64)) )
                              (X_set (t +i 1) 64 __tup_0)
                              (X_set t 64 __tup_1)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__40 ← (( do
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
              if (w__40 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__42 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
                  if (w__42 : Bool)
                  then
                    (do
                      let w__44 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__44 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then
                        (do
                          let w__45 ← (( do readReg TTBR1_EL2 ) : SailM (BitVec 128) )
                          let (__tup_0, __tup_1) ← (( do (Split w__45 64) ) : SailM
                            ((BitVec 64) × (BitVec 64)) )
                          (X_set (t +i 1) 64 __tup_0)
                          (X_set t 64 __tup_1))
                      else
                        (do
                          let w__46 ← (( do (TTBR1_EL1_read ()) ) : SailM (BitVec 128) )
                          let (__tup_0, __tup_1) ← (( do (Split w__46 64) ) : SailM
                            ((BitVec 64) × (BitVec 64)) )
                          (X_set (t +i 1) 64 __tup_0)
                          (X_set t 64 __tup_1)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__47 ← (( do (TTBR1_EL1_read ()) ) : SailM (BitVec 128) )
                  let (__tup_0, __tup_1) ← (( do (Split w__47 64) ) : SailM
                    ((BitVec 64) × (BitVec 64)) )
                  (X_set (t +i 1) 64 __tup_0)
                  (X_set t 64 __tup_1))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def VTTBR_EL2_SysRegRead128_a9b3226c12a0e07e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
          let w__7 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__5) +++ (_get_HCR_EL2_Type_NV w__6)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              let w__8 ← (( do (NVMem_read__1 (BitVec.toNat 0x020#12) 128) ) : SailM (BitVec 128)
                )
              let (__tup_0, __tup_1) ← (( do (Split w__8 64) ) : SailM
                ((BitVec 64) × (BitVec 64)) )
              (X_set (t +i 1) 64 __tup_0)
              (X_set t 64 __tup_1))
          else
            (do
              let w__10 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__17 ← (( do
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
              if (w__17 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__19 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
                  if (w__19 : Bool)
                  then
                    (do
                      let w__21 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__21 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                  else
                    (do
                      let w__22 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
                      let (__tup_0, __tup_1) ← (( do (Split w__22 64) ) : SailM
                        ((BitVec 64) × (BitVec 64)) )
                      (X_set (t +i 1) 64 __tup_0)
                      (X_set t 64 __tup_1))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__23 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
                  let (__tup_0, __tup_1) ← (( do (Split w__23 64) ) : SailM
                    ((BitVec 64) × (BitVec 64)) )
                  (X_set (t +i 1) 64 __tup_0)
                  (X_set t 64 __tup_1))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR0_EL1_SysRegWrite128_66ee61de597f133e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_D128En : (BitVec 1) := (_get_SCR_EL3_Type_D128En w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TVM : (BitVec 1) := (_get_HCR_EL2_Type_TVM w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR_EL2_TTBR0_EL1 : (BitVec 1) := (_get_HFGWTR_EL2_Type_TTBR0_EL1 w__5)
  let w__6 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_D128En : (BitVec 1) := (_get_HCRX_EL2_Type_D128En w__6)
  let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__7)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__14 ← (( do
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
          if (w__14 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__16 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TVM == 1#1) : Bool))) ) : SailM Bool )
              if (w__16 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else
                (do
                  let w__23 ← (( do
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
                                    let w__20 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__20) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HFGWTR_EL2_TTBR0_EL1 == 1#1) : Bool))) ) : SailM
                    Bool )
                  if (w__23 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      let w__27 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            (pure ((← do
                                  let w__25 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                                  (pure (((! w__25) : Bool)))) || ((__HCRX_EL2_D128En == 0#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__27 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                      else
                        (do
                          let w__29 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__29 : Bool)
                          then
                            (do
                              let w__31 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__31 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                          else
                            (do
                              let w__36 ← (( do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__33 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__34 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__35 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_NV2 w__33) +++ ((_get_HCR_EL2_Type_NV1
                                              w__34) +++ (_get_HCR_EL2_Type_NV w__35))) == 0b111#3) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__36 : Bool)
                              then
                                (do
                                  let w__37 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                                  let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  (NVMem_set__1 (BitVec.toNat 0x200#12) 128 (w__37 +++ w__38)))
                              else
                                (do
                                  let w__39 ← (( do (TTBR0_EL1_read ()) ) : SailM (BitVec 128) )
                                  let w__40 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                                  let w__41 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  (TTBR0_EL1_write
                                    (Mk_TTBR0_EL1_Type
                                      (Sail.BitVec.updateSubrange w__39 127 0 (w__40 +++ w__41)))))))))))
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
                      else (pure false)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
              if (w__48 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__50 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
                  if (w__50 : Bool)
                  then
                    (do
                      let w__52 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__52 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then
                        (do
                          let w__53 ← (( do (TTBR0_EL2_read ()) ) : SailM (BitVec 128) )
                          let w__54 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                          let w__55 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (TTBR0_EL2_write
                            (Mk_TTBR0_EL2_Type
                              (Sail.BitVec.updateSubrange w__53 127 0 (w__54 +++ w__55)))))
                      else
                        (do
                          let w__56 ← (( do (TTBR0_EL1_read ()) ) : SailM (BitVec 128) )
                          let w__57 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                          let w__58 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (TTBR0_EL1_write
                            (Mk_TTBR0_EL1_Type
                              (Sail.BitVec.updateSubrange w__56 127 0 (w__57 +++ w__58))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__59 ← (( do (TTBR0_EL1_read ()) ) : SailM (BitVec 128) )
                  let w__60 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                  let w__61 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (TTBR0_EL1_write
                    (Mk_TTBR0_EL1_Type (Sail.BitVec.updateSubrange w__59 127 0 (w__60 +++ w__61)))))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR0_EL1_SysRegWrite128_8ea27f288a4b152e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
  let w__3 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_D128En : (BitVec 1) := (_get_SCR_EL3_Type_D128En w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__9 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__6) +++ ((_get_HCR_EL2_Type_NV1 w__7) +++ (_get_HCR_EL2_Type_NV
                          w__8))) == 0b101#3) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__9 : Bool)
          then
            (do
              let w__10 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
              let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (NVMem_set__1 (BitVec.toNat 0x200#12) 128 (w__10 +++ w__11)))
          else
            (do
              let w__13 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__13 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
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
                          else (pure false)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__20 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__22 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
                      if (w__22 : Bool)
                      then
                        (do
                          let w__24 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__24 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                      else
                        (do
                          let w__25 ← (( do (TTBR0_EL1_read ()) ) : SailM (BitVec 128) )
                          let w__26 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                          let w__27 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (TTBR0_EL1_write
                            (Mk_TTBR0_EL1_Type
                              (Sail.BitVec.updateSubrange w__25 127 0 (w__26 +++ w__27)))))))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__31 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__29 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__29) : Bool))))
                          else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool))) ) : SailM Bool )
                  if (w__31 : Bool)
                  then
                    (do
                      let w__32 ← (( do (TTBR0_EL1_read ()) ) : SailM (BitVec 128) )
                      let w__33 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                      let w__34 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (TTBR0_EL1_write
                        (Mk_TTBR0_EL1_Type
                          (Sail.BitVec.updateSubrange w__32 127 0 (w__33 +++ w__34)))))
                  else sailThrow ((Error_Undefined ())))
              else (pure (())))))


end ArmFull.Functions
