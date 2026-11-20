module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0252
public import ArmFull.Fn.M0882
public import ArmFull.Fn.M0883 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: k_advsimd : Bool, k_include_fpexc_check_name : Bool -/
def CheckAdvSIMDOrVFPEnabled (include_fpexc_check_name : Bool) (advsimd : Bool) : SailM Unit := do
  (AArch32_CheckAdvSIMDOrFPEnabled include_fpexc_check_name advsimd)


/-- Type quantifiers: k_include_fpexc_check_name : Bool -/
def CheckVFPEnabled (include_fpexc_check_name : Bool) : SailM Unit := do
  let advsimd : Bool := false
  (AArch32_CheckAdvSIMDOrFPEnabled include_fpexc_check_name advsimd)


/-- Type quantifiers: t : Int -/
def AT_S12E0R_SysOpsWrite_0c5b1bd4a1d08392 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__8 ← (( do
                if ((← do
                     let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                     let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                     (pure (((((_get_HCR_EL2_Type_E2H w__4) +++ (_get_HCR_EL2_Type_TGE w__5)) == 0b11#2) : Bool)))) : Bool)
                then (pure true)
                else
                  (do
                    let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_DC w__6) +++ (_get_HCR_EL2_Type_VM w__7)) == 0b00#2) : Bool))))
                ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  let w__9 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_AT w__9 TranslationStage_1 EL0 ATAccess_Read))
              else
                (do
                  let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_AT w__10 TranslationStage_12 EL0 ATAccess_Read)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__11 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__11) : Bool)
                  then
                    (do
                      let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_AT w__12 TranslationStage_1 EL0 ATAccess_Read))
                  else
                    (do
                      let w__19 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            if ((← do
                                 let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 (pure (((((_get_HCR_EL2_Type_E2H w__14) +++ (_get_HCR_EL2_Type_TGE
                                         w__15)) == 0b11#2) : Bool)))) : Bool)
                            then (pure true)
                            else
                              (do
                                let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                (pure (((((_get_HCR_EL2_Type_DC w__16) +++ (_get_HCR_EL2_Type_VM
                                        w__17)) == 0b00#2) : Bool)))))
                        else (pure false) ) : SailM Bool )
                      if (w__19 : Bool)
                      then
                        (do
                          let w__20 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_AT w__20 TranslationStage_1 EL0 ATAccess_Read))
                      else
                        (do
                          let w__21 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_AT w__21 TranslationStage_12 EL0 ATAccess_Read))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def AT_S12E0W_SysOpsWrite_ebaedef9bc851c96 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__8 ← (( do
                if ((← do
                     let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                     let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                     (pure (((((_get_HCR_EL2_Type_E2H w__4) +++ (_get_HCR_EL2_Type_TGE w__5)) == 0b11#2) : Bool)))) : Bool)
                then (pure true)
                else
                  (do
                    let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_DC w__6) +++ (_get_HCR_EL2_Type_VM w__7)) == 0b00#2) : Bool))))
                ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  let w__9 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_AT w__9 TranslationStage_1 EL0 ATAccess_Write))
              else
                (do
                  let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_AT w__10 TranslationStage_12 EL0 ATAccess_Write)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__11 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__11) : Bool)
                  then
                    (do
                      let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_AT w__12 TranslationStage_1 EL0 ATAccess_Write))
                  else
                    (do
                      let w__19 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            if ((← do
                                 let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 (pure (((((_get_HCR_EL2_Type_E2H w__14) +++ (_get_HCR_EL2_Type_TGE
                                         w__15)) == 0b11#2) : Bool)))) : Bool)
                            then (pure true)
                            else
                              (do
                                let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                (pure (((((_get_HCR_EL2_Type_DC w__16) +++ (_get_HCR_EL2_Type_VM
                                        w__17)) == 0b00#2) : Bool)))))
                        else (pure false) ) : SailM Bool )
                      if (w__19 : Bool)
                      then
                        (do
                          let w__20 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_AT w__20 TranslationStage_1 EL0 ATAccess_Write))
                      else
                        (do
                          let w__21 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_AT w__21 TranslationStage_12 EL0 ATAccess_Write))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def AT_S12E1R_SysOpsWrite_90c7bc3b4c4e8ad2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__8 ← (( do
                if ((← do
                     let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                     let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                     (pure (((((_get_HCR_EL2_Type_E2H w__4) +++ (_get_HCR_EL2_Type_TGE w__5)) == 0b11#2) : Bool)))) : Bool)
                then (pure true)
                else
                  (do
                    let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_DC w__6) +++ (_get_HCR_EL2_Type_VM w__7)) == 0b00#2) : Bool))))
                ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  let w__9 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_AT w__9 TranslationStage_1 EL1 ATAccess_Read))
              else
                (do
                  let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_AT w__10 TranslationStage_12 EL1 ATAccess_Read)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__11 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__11) : Bool)
                  then
                    (do
                      let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_AT w__12 TranslationStage_1 EL1 ATAccess_Read))
                  else
                    (do
                      let w__19 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            if ((← do
                                 let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 (pure (((((_get_HCR_EL2_Type_E2H w__14) +++ (_get_HCR_EL2_Type_TGE
                                         w__15)) == 0b11#2) : Bool)))) : Bool)
                            then (pure true)
                            else
                              (do
                                let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                (pure (((((_get_HCR_EL2_Type_DC w__16) +++ (_get_HCR_EL2_Type_VM
                                        w__17)) == 0b00#2) : Bool)))))
                        else (pure false) ) : SailM Bool )
                      if (w__19 : Bool)
                      then
                        (do
                          let w__20 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_AT w__20 TranslationStage_1 EL1 ATAccess_Read))
                      else
                        (do
                          let w__21 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_AT w__21 TranslationStage_12 EL1 ATAccess_Read))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def AT_S12E1W_SysOpsWrite_1152e7884348cb33 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__8 ← (( do
                if ((← do
                     let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                     let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                     (pure (((((_get_HCR_EL2_Type_E2H w__4) +++ (_get_HCR_EL2_Type_TGE w__5)) == 0b11#2) : Bool)))) : Bool)
                then (pure true)
                else
                  (do
                    let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_DC w__6) +++ (_get_HCR_EL2_Type_VM w__7)) == 0b00#2) : Bool))))
                ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  let w__9 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_AT w__9 TranslationStage_1 EL1 ATAccess_Write))
              else
                (do
                  let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_AT w__10 TranslationStage_12 EL1 ATAccess_Write)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__11 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__11) : Bool)
                  then
                    (do
                      let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_AT w__12 TranslationStage_1 EL1 ATAccess_Write))
                  else
                    (do
                      let w__19 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            if ((← do
                                 let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 (pure (((((_get_HCR_EL2_Type_E2H w__14) +++ (_get_HCR_EL2_Type_TGE
                                         w__15)) == 0b11#2) : Bool)))) : Bool)
                            then (pure true)
                            else
                              (do
                                let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                (pure (((((_get_HCR_EL2_Type_DC w__16) +++ (_get_HCR_EL2_Type_VM
                                        w__17)) == 0b00#2) : Bool)))))
                        else (pure false) ) : SailM Bool )
                      if (w__19 : Bool)
                      then
                        (do
                          let w__20 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_AT w__20 TranslationStage_1 EL1 ATAccess_Write))
                      else
                        (do
                          let w__21 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_AT w__21 TranslationStage_12 EL1 ATAccess_Write))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def AT_S1E0R_SysOpsWrite_40187a824e445931 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_AT : (BitVec 1) := (_get_HCR_EL2_Type_AT w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_ATS1E0R : (BitVec 1) := (_get_HFGITR_EL2_Type_ATS1E0R w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_AT == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__12 ← (( do
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
                                let w__9 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__9) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGITR_EL2_ATS1E0R == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__12 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_AT w__13 TranslationStage_1 EL0 ATAccess_Read))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__14 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_AT w__14 TranslationStage_1 EL0 ATAccess_Read))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__15 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_AT w__15 TranslationStage_1 EL0 ATAccess_Read))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def AT_S1E0W_SysOpsWrite_5d5981498f3ff63f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_AT : (BitVec 1) := (_get_HCR_EL2_Type_AT w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_ATS1E0W : (BitVec 1) := (_get_HFGITR_EL2_Type_ATS1E0W w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_AT == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__12 ← (( do
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
                                let w__9 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__9) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGITR_EL2_ATS1E0W == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__12 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_AT w__13 TranslationStage_1 EL0 ATAccess_Write))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__14 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_AT w__14 TranslationStage_1 EL0 ATAccess_Write))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__15 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_AT w__15 TranslationStage_1 EL0 ATAccess_Write))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def AT_S1E1RP_SysOpsWrite_597c8bbb547c9cc7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_AT : (BitVec 1) := (_get_HCR_EL2_Type_AT w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_ATS1E1RP : (BitVec 1) := (_get_HFGITR_EL2_Type_ATS1E1RP w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_AT == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__12 ← (( do
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
                                let w__9 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__9) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGITR_EL2_ATS1E1RP == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__12 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_AT w__13 TranslationStage_1 EL1 ATAccess_ReadPAN))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__14 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_AT w__14 TranslationStage_1 EL1 ATAccess_ReadPAN))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__15 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_AT w__15 TranslationStage_1 EL1 ATAccess_ReadPAN))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def AT_S1E1R_SysOpsWrite_efb944f010174dbe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_AT : (BitVec 1) := (_get_HCR_EL2_Type_AT w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_ATS1E1R : (BitVec 1) := (_get_HFGITR_EL2_Type_ATS1E1R w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_AT == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__12 ← (( do
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
                                let w__9 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__9) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGITR_EL2_ATS1E1R == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__12 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_AT w__13 TranslationStage_1 EL1 ATAccess_Read))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__14 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_AT w__14 TranslationStage_1 EL1 ATAccess_Read))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__15 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_AT w__15 TranslationStage_1 EL1 ATAccess_Read))
              else (pure (())))))


end ArmFull.Functions
