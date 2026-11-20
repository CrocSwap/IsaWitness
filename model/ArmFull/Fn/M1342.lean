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
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0058
public import ArmFull.Fn.M0063
public import ArmFull.Fn.M0073
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0124
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0172
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0202
public import ArmFull.Fn.M0208
public import ArmFull.Fn.M0252
public import ArmFull.Fn.M1235
public import ArmFull.Fn.M1236
public import ArmFull.Fn.M1237 set_option backward.proofsInPublic true @[expose] public section

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
def TTBR1_EL1_SysRegWrite128_d20c29029eb4ed94 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              (NVMem_set__1 (BitVec.toNat 0x210#12) 128 (w__10 +++ w__11)))
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
                          let w__25 ← (( do (TTBR1_EL1_read ()) ) : SailM (BitVec 128) )
                          let w__26 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                          let w__27 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (TTBR1_EL1_write
                            (Mk_TTBR1_EL1_Type
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
                      let w__32 ← (( do (TTBR1_EL1_read ()) ) : SailM (BitVec 128) )
                      let w__33 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                      let w__34 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (TTBR1_EL1_write
                        (Mk_TTBR1_EL1_Type
                          (Sail.BitVec.updateSubrange w__32 127 0 (w__33 +++ w__34)))))
                  else sailThrow ((Error_Undefined ())))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TTBR1_EL2_SysRegWrite128_4bfd1913f2c26b7d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
  let __HFGWTR_EL2_TTBR1_EL1 : (BitVec 1) := (_get_HFGWTR_EL2_Type_TTBR1_EL1 w__5)
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
                      (EL2Enabled ())) && ((__HCR_EL2_TVM == 1#1) : Bool))) ) : SailM Bool )
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
                          else (pure false)) && ((__HFGWTR_EL2_TTBR1_EL1 == 1#1) : Bool))) ) : SailM
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
                              let w__32 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                              let w__33 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (NVMem_set__1 (BitVec.toNat 0x210#12) 128 (w__32 +++ w__33)))
                          else
                            (do
                              let w__34 ← (( do (TTBR1_EL1_read ()) ) : SailM (BitVec 128) )
                              let w__35 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                              let w__36 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (TTBR1_EL1_write
                                (Mk_TTBR1_EL1_Type
                                  (Sail.BitVec.updateSubrange w__34 127 0 (w__35 +++ w__36))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__43 ← (( do
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
              if (w__43 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__45 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
                  if (w__45 : Bool)
                  then
                    (do
                      let w__47 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__47 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then
                        (do
                          let w__48 ← (( do readReg TTBR1_EL2 ) : SailM (BitVec 128) )
                          let w__49 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                          let w__50 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg TTBR1_EL2 (Sail.BitVec.updateSubrange w__48 127 0
                            (w__49 +++ w__50)))
                      else
                        (do
                          let w__51 ← (( do (TTBR1_EL1_read ()) ) : SailM (BitVec 128) )
                          let w__52 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                          let w__53 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (TTBR1_EL1_write
                            (Mk_TTBR1_EL1_Type
                              (Sail.BitVec.updateSubrange w__51 127 0 (w__52 +++ w__53))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__54 ← (( do (TTBR1_EL1_read ()) ) : SailM (BitVec 128) )
                  let w__55 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                  let w__56 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (TTBR1_EL1_write
                    (Mk_TTBR1_EL1_Type (Sail.BitVec.updateSubrange w__54 127 0 (w__55 +++ w__56)))))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def VTTBR_EL2_SysRegWrite128_3ec09d9d33270957 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
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
              let w__8 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
              let w__9 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (NVMem_set__1 (BitVec.toNat 0x020#12) 128 (w__8 +++ w__9)))
          else
            (do
              let w__11 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__11 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__18 ← (( do
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
              if (w__18 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__20 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__SCR_EL3_D128En == 0#1) : Bool))) ) : SailM Bool )
                  if (w__20 : Bool)
                  then
                    (do
                      let w__22 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__22 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x14#8))))
                  else
                    (do
                      let w__23 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
                      let w__24 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                      let w__25 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (VTTBR_EL2_write
                        (Mk_VTTBR_EL2_Type
                          (Sail.BitVec.updateSubrange w__23 127 0 (w__24 +++ w__25)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__26 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
                  let w__27 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
                  let w__28 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (VTTBR_EL2_write
                    (Mk_VTTBR_EL2_Type (Sail.BitVec.updateSubrange w__26 127 0 (w__27 +++ w__28)))))
              else (pure (())))))


def decode_aarch32_instrs_LDM_A1enc_A_txt (cond : (BitVec 4)) (W : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 16)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:3589.29-3589.30"
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 16) := register_list
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers
                 (Sail.Int.toNatChecked (n)))])) == 1#1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDM_Op_A_txt (Sail.Int.toNatChecked (n)) registers wback))
  else (pure (()))


def decode_aarch32_instrs_LDM_T1enc_A_txt (Rn : (BitVec 3)) (register_list : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 16) := (0b00000000#8 +++ register_list)
      let wback : Bool :=
        ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers (Sail.Int.toNatChecked (n)))])) == 0#1)
      if (((BitCount registers) <b 1) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDM_Op_A_txt (Sail.Int.toNatChecked (n)) registers wback))
  else (pure (()))


def decode_aarch32_instrs_LDM_T2enc_A_txt (W : (BitVec 1)) (Rn : (BitVec 4)) (P : (BitVec 1)) (M : (BitVec 1)) (register_list : (BitVec 14)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 16) := ((P +++ M) +++ register_list)
      let wback : Bool := (W == 1#1)
      if ((((n == 15) || ((BitCount registers) <b 2)) || ((P == 1#1) && (M == 1#1))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers
                 (Sail.Int.toNatChecked (n)))])) == 1#1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers 13)])) == 1#1) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__4 ← (( do
        if ((← do
             if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers 15)])) == 1#1) : Bool) : Bool)
             then
               (do
                 (InITBlock ()))
             else (pure false)) : Bool)
        then
          (do
            let w__3 ← (( do (LastInITBlock ()) ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDM_Op_A_txt (Sail.Int.toNatChecked (n)) registers wback))
  else (pure (()))


def decode_aarch32_instrs_LDMDA_A1enc_A_txt (cond : (BitVec 4)) (W : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 16)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:3697.29-3697.30"
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 16) := register_list
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers
                 (Sail.Int.toNatChecked (n)))])) == 1#1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDMDA_Op_A_txt (Sail.Int.toNatChecked (n)) registers wback))
  else (pure (()))


def decode_aarch32_instrs_LDMDB_A1enc_A_txt (cond : (BitVec 4)) (W : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 16)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:3749.29-3749.30"
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 16) := register_list
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers
                 (Sail.Int.toNatChecked (n)))])) == 1#1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDMDB_Op_A_txt (Sail.Int.toNatChecked (n)) registers wback))
  else (pure (()))


def decode_aarch32_instrs_LDMDB_T1enc_A_txt (W : (BitVec 1)) (Rn : (BitVec 4)) (P : (BitVec 1)) (M : (BitVec 1)) (register_list : (BitVec 14)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 16) := ((P +++ M) +++ register_list)
      let wback : Bool := (W == 1#1)
      if ((((n == 15) || ((BitCount registers) <b 2)) || ((P == 1#1) && (M == 1#1))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers
                 (Sail.Int.toNatChecked (n)))])) == 1#1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers 13)])) == 1#1) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__4 ← (( do
        if ((← do
             if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers 15)])) == 1#1) : Bool) : Bool)
             then
               (do
                 (InITBlock ()))
             else (pure false)) : Bool)
        then
          (do
            let w__3 ← (( do (LastInITBlock ()) ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDMDB_Op_A_txt (Sail.Int.toNatChecked (n)) registers wback))
  else (pure (()))


def decode_aarch32_instrs_LDMIB_A1enc_A_txt (cond : (BitVec 4)) (W : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 16)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:3835.29-3835.30"
      let n : Int := (BitVec.toNat Rn)
      let registers : (BitVec 16) := register_list
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers
                 (Sail.Int.toNatChecked (n)))])) == 1#1)) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDMIB_Op_A_txt (Sail.Int.toNatChecked (n)) registers wback))
  else (pure (()))


def decode_aarch32_instrs_LDRB_i_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:3881.29-3881.30"
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDRB (literal)"))
      else (pure (()))
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then sailThrow ((Error_See "LDRBT"))
      else (pure (()))
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (((t == 15) || (wback && (n == t))) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDRB_i_OpA_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDRB_i_T1enc_A_txt (imm5 : (BitVec 5)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let n : Int := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm5 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      (execute_aarch32_instrs_LDRB_i_OpT_A_txt add imm32 index (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t)) wback))
  else (pure (()))


end ArmFull.Functions
