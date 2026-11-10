import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0045
import ArmFull.Fn.M0048
import ArmFull.Fn.M0051
import ArmFull.Fn.M0061
import ArmFull.Fn.M0092
import ArmFull.Fn.M0124
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0172
import ArmFull.Fn.M0180
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
import ArmFull.Fn.M0185
import ArmFull.Fn.M0186
import ArmFull.Fn.M0197
import ArmFull.Fn.M0216
import ArmFull.Fn.M0228
import ArmFull.Fn.M0237
import ArmFull.Fn.M0250
import ArmFull.Fn.M0254
import ArmFull.Fn.M0255
import ArmFull.Fn.M0852
import ArmFull.Fn.M0853

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

def AArch64_IC__1 (regval : (BitVec 64)) (opscope : CacheOpScope) : SailM Unit := SailME.run do
  let ss ← (( do (undefined_SecurityState (← occLabel 2490) ()) ) : SailME Unit SecurityState )
  let cache ← (( do (undefined_CacheRecord (← occLabel 2491) ()) ) : SailME Unit CacheRecord )
  let cache : CacheRecord := { cache with acctype := AccessType_IC }
  let cache : CacheRecord := { cache with cachetype := CacheType_Instruction }
  let cache : CacheRecord := { cache with cacheop := CacheOp_Invalidate }
  let cache : CacheRecord := { cache with opscope := opscope }
  if (((BEq.beq opscope CacheOpScope_ALLU) || (BEq.beq opscope CacheOpScope_ALLUIS)) : Bool)
  then
    (do
      let w__0 ← (( do readReg PSTATE ) : SailME Unit ProcState )
      let ss ← (( do (SecurityStateAtEL w__0.EL) ) : SailME Unit SecurityState )
      let cache : CacheRecord := { cache with cpas := (CPASAtSecurityState ss) }
      let w__7 ← (( do
        if (((BEq.beq opscope CacheOpScope_ALLUIS) : Bool) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 if ((← do
                      if (((BEq.beq opscope CacheOpScope_ALLU) : Bool) : Bool)
                      then
                        (do
                          let w__1 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                          (pure (((w__1.EL == EL1) : Bool))))
                      else (pure false)) : Bool)
                 then
                   (do
                     (EL2Enabled ()))
                 else (pure false)) : Bool)
            then
              (do
                let w__5 ← (( do readReg HCR_EL2 ) : SailME Unit (BitVec 64) )
                (pure ((((_get_HCR_EL2_Type_FB w__5) == 1#1) : Bool))))
            else (pure false)) ) : SailME Unit Bool )
      let cache : CacheRecord :=
        if (w__7 : Bool)
        then { cache with shareability := Shareability_ISH }
        else { cache with shareability := Shareability_NSH }
      let cache : CacheRecord := { cache with regval := regval }
      (CACHE_OP cache))
  else
    (do
      ArmFull.assert (BEq.beq opscope CacheOpScope_PoU) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:36768.42-36768.43"
      let w__10 ← (( do
        if ((← do
             (EL2Enabled ())) : Bool)
        then
          (do
            let w__9 ← (( do (IsInHost ()) ) : SailME Unit Bool )
            (pure (((! w__9) : Bool))))
        else (pure false) ) : SailME Unit Bool )
      let cache ← (( do
        if (w__10 : Bool)
        then
          (do
            let w__13 ← (( do
              if ((← do
                   let w__11 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                   (pure (((w__11.EL == EL0) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__12 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                  (pure (((w__12.EL == EL1) : Bool)))) ) : SailME Unit Bool )
            if (w__13 : Bool)
            then
              (do
                let cache : CacheRecord := { cache with is_vmid_valid := true }
                let w__14 ← (( do (VMID_read ()) ) : SailME Unit (BitVec 16) )
                let cache := ({ cache with vmid := w__14 } : CacheRecord)
                (pure (cache)))
            else
              (let cache : CacheRecord := { cache with is_vmid_valid := false }
              (pure (cache))))
        else
          (let cache : CacheRecord := { cache with is_vmid_valid := false }
          (pure (cache))) ) : SailME Unit CacheRecord )
      let w__15 ← (( do readReg PSTATE ) : SailME Unit ProcState )
      let cache ← (( do
        if ((w__15.EL == EL0) : Bool)
        then
          (do
            let cache : CacheRecord := { cache with is_asid_valid := true }
            let w__16 ← (( do (ASID_read ()) ) : SailME Unit (BitVec 16) )
            let cache := ({ cache with asid := w__16 } : CacheRecord)
            (pure (cache)))
        else
          (let cache : CacheRecord := { cache with is_asid_valid := false }
          (pure (cache))) ) : SailME Unit CacheRecord )
      let vaddress : (BitVec 64) := regval
      let need_translate ← (( do (ICInstNeedsTranslation opscope) ) : SailME Unit Bool )
      let cache : CacheRecord := { cache with vaddress := regval }
      let cache : CacheRecord := { cache with shareability := Shareability_NSH }
      let cache : CacheRecord := { cache with translated := need_translate }
      if ((! need_translate) : Bool)
      then
        (do
          let w__17 ← (( do (__UNKNOWN_FullAddress ()) ) : SailME Unit FullAddress )
          let cache := ({ cache with paddress := w__17 } : CacheRecord)
          (CACHE_OP cache)
          SailME.throw (() : Unit))
      else
        (do
          let accdesc ← (( do (CreateAccDescIC cache) ) : SailME Unit AccessDescriptor )
          let aligned : Bool := true
          let size : Nat := 0
          let memaddrdesc ← (( do (AArch64_TranslateAddress vaddress accdesc aligned size) ) :
            SailME Unit AddressDescriptor )
          if ((IsFault memaddrdesc) : Bool)
          then
            (do
              (AArch64_Abort regval memaddrdesc.fault))
          else (pure (()))
          let cache : CacheRecord := { cache with cpas := (CPASAtPAS memaddrdesc.paddress.paspace) }
          let cache : CacheRecord := { cache with paddress := memaddrdesc.paddress }
          (CACHE_OP cache)))


/-- Type quantifiers: k_aligned : Bool, size : Int -/
def AArch32_TranslateAddress (va : (BitVec 32)) (accdesc : AccessDescriptor) (aligned : Bool) (size : Int) : SailM AddressDescriptor := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let regime ← (( do (TranslationRegime w__0.EL) ) : SailM Regime )
  let w__1 ← (( do (RegimeUsingAArch32 regime) ) : SailM Bool )
  if ((! w__1) : Bool)
  then
    (do
      (AArch64_TranslateAddress (Sail.BitVec.zeroExtend va 64) accdesc aligned size))
  else
    (do
      let regime ← (( do (TranslationRegime accdesc.el) ) : SailM Regime )
      let tsi ← (( do (AArch32_GetTranslationStartInfo regime accdesc.ss accdesc va size) ) :
        SailM TranslationStartInfo )
      (start_translation tsi)
      let result ← (( do (AArch32_FullTranslate va accdesc aligned) ) : SailM AddressDescriptor )
      let result ← (( do
        if ((! (IsFault result)) : Bool)
        then
          (do
            let w__3 ← (( do (AArch32_CheckDebug va accdesc size) ) : SailM FaultRecord )
            let result := ({ result with fault := w__3 } : AddressDescriptor)
            (pure (result)))
        else (pure (result)) ) : SailM AddressDescriptor )
      let result : AddressDescriptor := { result with vaddress := (Sail.BitVec.zeroExtend va 64) }
      (end_translation result)
      (pure (result)))


def CheckAdvSIMDEnabled (_ : Unit) : SailM Unit := do
  let fpexc_check : Bool := true
  let advsimd : Bool := true
  (AArch32_CheckAdvSIMDOrFPEnabled fpexc_check advsimd)
  let loop_i_lower : Nat := 0
  let loop_i_upper : Nat := 31
  (do
    let mut loop_vars := ()
    for i in [loop_i_lower:loop_i_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do readReg _Dclone ) : SailM (Vector (BitVec 64) 32) )
        let w__1 ← (( do (D_read i) ) : SailM (BitVec 64) )
        writeReg _Dclone (vectorUpdate w__0 (Sail.Int.toNatChecked (i)) w__1)
    (pure loop_vars))


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
              let w__10 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_ATS1E0R == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_AT w__11 TranslationStage_1 EL0 ATAccess_Read))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_AT w__12 TranslationStage_1 EL0 ATAccess_Read))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_AT w__13 TranslationStage_1 EL0 ATAccess_Read))
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
              let w__10 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_ATS1E0W == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_AT w__11 TranslationStage_1 EL0 ATAccess_Write))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_AT w__12 TranslationStage_1 EL0 ATAccess_Write))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_AT w__13 TranslationStage_1 EL0 ATAccess_Write))
              else (pure (())))))


end ArmFull.Functions
