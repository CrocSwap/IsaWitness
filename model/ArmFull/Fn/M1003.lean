import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0041
import ArmFull.Fn.M0048
import ArmFull.Fn.M0051
import ArmFull.Fn.M0063
import ArmFull.Fn.M0092
import ArmFull.Fn.M0097
import ArmFull.Fn.M0124
import ArmFull.Fn.M0146
import ArmFull.Fn.M0154
import ArmFull.Fn.M0168
import ArmFull.Fn.M0181
import ArmFull.Fn.M0218
import ArmFull.Fn.M0237
import ArmFull.Fn.M0244
import ArmFull.Fn.M0254
import ArmFull.Fn.M0580
import ArmFull.Fn.M0851
import ArmFull.Fn.M0924
import ArmFull.Fn.M0925

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

def CheckCryptoEnabled32 (_ : Unit) : SailM Unit := do
  (CheckAdvSIMDEnabled ())


/-- Type quantifiers: k_aligned : Bool, k_ispair : Bool, size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def AArch32_MemSingle_read__1 (address : (BitVec 32)) (size : Nat) (accdesc_in : AccessDescriptor) (aligned : Bool) (ispair : Bool) : SailM (BitVec (size * 8)) := do
  ArmFull.assert ((size == 1) || ((size == 2) || ((size == 4) || ((size == 8) || (size == 16))))) "sail-arm/v8_base.sail:41910.69-41910.70"
  let value_name ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 2761)
      (Sail.Int.toNatChecked ((size *i 8))))) ) : SailM (BitVec (size * 8)) )
  let accdesc : AccessDescriptor := accdesc_in
  ArmFull.assert (IsAligned__1 address size) "sail-arm/v8_base.sail:41913.38-41913.39"
  let memaddrdesc ← (( do (AArch32_TranslateAddress address accdesc aligned size) ) : SailM
    AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then
    (do
      (AArch32_Abort address memaddrdesc.fault))
  else (pure (()))
  let w__0 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let is_load : Bool := true
      (SPESampleLoadStore is_load accdesc memaddrdesc))
  else (pure (()))
  let memstatus ← (( do (undefined_PhysMemRetStatus (← occLabel 2762) ()) ) : SailM
    PhysMemRetStatus )
  let w__1 ← (( do
    ((fun (x0, x1) => (x0, (Sail.BitVec.castWidth x1))) <$> (PhysMemRead memaddrdesc size accdesc
      none)) ) : SailM (PhysMemRetStatus × (BitVec (8 * size))) )
  let (tup__0, tup__1) := (w__1 : (PhysMemRetStatus × (BitVec (8 * size))))
  let memstatus : PhysMemRetStatus := tup__0
  let value_name : (BitVec (size * 8)) := (Sail.BitVec.castWidth tup__1)
  if ((IsFault__2 memstatus) : Bool)
  then
    (do
      (HandleExternalReadAbort memstatus memaddrdesc size accdesc))
  else (pure (()))
  (pure ((Sail.BitVec.castWidth value_name)))


/-- Type quantifiers: k_aligned : Bool, k_ispair : Bool, size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def AArch32_MemSingle_set__1 (address : (BitVec 32)) (size : Nat) (accdesc_in : AccessDescriptor) (aligned : Bool) (ispair : Bool) (value_name : (BitVec (size * 8))) : SailM Unit := do
  ArmFull.assert ((size == 1) || ((size == 2) || ((size == 4) || ((size == 8) || (size == 16))))) "sail-arm/v8_base.sail:41945.69-41945.70"
  let accdesc : AccessDescriptor := accdesc_in
  ArmFull.assert (IsAligned__1 address size) "sail-arm/v8_base.sail:41947.38-41947.39"
  let memaddrdesc ← (( do (AArch32_TranslateAddress address accdesc aligned size) ) : SailM
    AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then
    (do
      (AArch32_Abort address memaddrdesc.fault))
  else (pure (()))
  let _ : Unit :=
    if ((bne memaddrdesc.memattrs.shareability Shareability_NSH) : Bool)
    then (ClearExclusiveByAddress memaddrdesc.paddress (ProcessorID ()) size)
    else ()
  let w__0 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let is_load : Bool := false
      (SPESampleLoadStore is_load accdesc memaddrdesc))
  else (pure (()))
  let memstatus ← (( do
    (PhysMemWrite memaddrdesc size accdesc none (Sail.BitVec.castWidth value_name)) ) : SailM
    PhysMemRetStatus )
  if ((IsFault__2 memstatus) : Bool)
  then
    (do
      (HandleExternalWriteAbort memstatus memaddrdesc size accdesc))
  else (pure (()))


/-- Type quantifiers: size : Int -/
def AArch32_SetExclusiveMonitors (address : (BitVec 32)) (size : Int) : SailM Unit := do
  writeReg __ExclusiveMonitorSet true
  let acqrel : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescExLDST MemOp_LOAD acqrel tagchecked) ) : SailM
    AccessDescriptor )
  let aligned : Bool := (IsAligned__1 address size)
  if ((! aligned) : Bool)
  then
    (do
      let w__0 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch32_Abort address w__0))
  else (pure (()))
  let memaddrdesc ← (( do (AArch32_TranslateAddress address accdesc aligned size) ) : SailM
    AddressDescriptor )
  (pure (if ((IsFault memaddrdesc) : Bool)
    then ()
    else
      (let _ : Unit :=
        if ((bne memaddrdesc.memattrs.shareability Shareability_NSH) : Bool)
        then (MarkExclusiveGlobal memaddrdesc.paddress (ProcessorID ()) size)
        else ()
      let _ : Unit := (MarkExclusiveLocal memaddrdesc.paddress (ProcessorID ()) size)
      (AArch32_MarkExclusiveVA address (ProcessorID ()) size))))


/-- Type quantifiers: size : Int -/
def AArch32_ExclusiveMonitorsPass (address : (BitVec 32)) (size : Int) : SailM Bool := do
  let acqrel : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescExLDST MemOp_STORE acqrel tagchecked) ) : SailM
    AccessDescriptor )
  let aligned : Bool := (IsAligned__1 address size)
  if ((! aligned) : Bool)
  then
    (do
      let w__0 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch32_Abort address w__0))
  else (pure (()))
  let w__1 ← (( do (AArch32_IsExclusiveVA address (ProcessorID ()) size) ) : SailM Bool )
  if ((! w__1) : Bool)
  then (pure (false))
  else
    (do
      let memaddrdesc ← (( do (AArch32_TranslateAddress address accdesc aligned size) ) : SailM
        AddressDescriptor )
      if ((IsFault memaddrdesc) : Bool)
      then
        (do
          (AArch32_Abort address memaddrdesc.fault))
      else (pure (()))
      let passed ← (( do (IsExclusiveLocal memaddrdesc.paddress (ProcessorID ()) size) ) : SailM
        Bool )
      let _ : Unit := (ClearExclusiveLocal (ProcessorID ()))
      if ((passed && (bne memaddrdesc.memattrs.shareability Shareability_NSH)) : Bool)
      then
        (do
          (IsExclusiveGlobal memaddrdesc.paddress (ProcessorID ()) size))
      else (pure (passed)))


/-- Type quantifiers: t : Int -/
def DC_CGDSW_SysOpsWrite_928589dc16baf135 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TSW : (BitVec 1) := (_get_HCR_EL2_Type_TSW w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_DCCSW : (BitVec 1) := (_get_HFGITR_EL2_Type_DCCSW w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TSW == 1#1) : Bool))) ) : SailM Bool )
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
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_DCCSW == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__11 CacheType_Data_Tag CacheOp_Clean CacheOpScope_SetWay))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_DC w__12 CacheType_Data_Tag CacheOp_Clean CacheOpScope_SetWay))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__13 CacheType_Data_Tag CacheOp_Clean CacheOpScope_SetWay))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DC_CGDVAC_SysOpsWrite_ec22b0e1f02114c3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_UCI : (BitVec 1) := (_get_SCTLR_EL1_Type_UCI w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TPCP : (BitVec 1) := (_get_HCR_EL2_Type_TPCP w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_DCCVAC : (BitVec 1) := (_get_HFGITR_EL2_Type_DCCVAC w__5)
  let w__6 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let __SCTLR_EL2_UCI : (BitVec 1) := (_get_SCTLR_EL2_Type_UCI w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__11 ← (( do
        (pure ((← do
              let w__10 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_E2H w__8) +++ (_get_HCR_EL2_Type_TGE w__9)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              (pure (((! w__10) : Bool)))) && ((__SCTLR_EL1_UCI == 0#1) : Bool))) ) : SailM Bool )
      if (w__11 : Bool)
      then
        (do
          let w__13 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else
        (do
          let w__18 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_E2H w__15) +++ (_get_HCR_EL2_Type_TGE w__16)) != 0b11#2) : Bool))))
                  else (pure false)) && ((__HCR_EL2_TPCP == 1#1) : Bool))) ) : SailM Bool )
          if (w__18 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__26 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     let w__20 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     let w__21 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     (pure (((((_get_HCR_EL2_Type_E2H w__20) +++ (_get_HCR_EL2_Type_TGE
                                             w__21)) != 0b11#2) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_DCCVAC == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__26 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__31 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__29 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__28) +++ (_get_HCR_EL2_Type_TGE
                                      w__29)) == 0b11#2) : Bool))))
                          else (pure false)) && ((__SCTLR_EL2_UCI == 0#1) : Bool))) ) : SailM Bool )
                  if (w__31 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__32 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_DC w__32 CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoC))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__34 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TPCP == 1#1) : Bool))) ) : SailM Bool )
          if (w__34 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__39 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_DCCVAC == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__39 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__40 CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoC))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__41 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_DC w__41 CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoC))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__42 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__42 CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoC))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DC_CGDVADP_SysOpsWrite_8e52ffae1d90dad3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_UCI : (BitVec 1) := (_get_SCTLR_EL1_Type_UCI w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TPCP : (BitVec 1) := (_get_HCR_EL2_Type_TPCP w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_DCCVADP : (BitVec 1) := (_get_HFGITR_EL2_Type_DCCVADP w__5)
  let w__6 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let __SCTLR_EL2_UCI : (BitVec 1) := (_get_SCTLR_EL2_Type_UCI w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__11 ← (( do
        (pure ((← do
              let w__10 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_E2H w__8) +++ (_get_HCR_EL2_Type_TGE w__9)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              (pure (((! w__10) : Bool)))) && ((__SCTLR_EL1_UCI == 0#1) : Bool))) ) : SailM Bool )
      if (w__11 : Bool)
      then
        (do
          let w__13 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else
        (do
          let w__18 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_E2H w__15) +++ (_get_HCR_EL2_Type_TGE w__16)) != 0b11#2) : Bool))))
                  else (pure false)) && ((__HCR_EL2_TPCP == 1#1) : Bool))) ) : SailM Bool )
          if (w__18 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__26 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     let w__20 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     let w__21 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     (pure (((((_get_HCR_EL2_Type_E2H w__20) +++ (_get_HCR_EL2_Type_TGE
                                             w__21)) != 0b11#2) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_DCCVADP == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__26 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__31 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__29 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__28) +++ (_get_HCR_EL2_Type_TGE
                                      w__29)) == 0b11#2) : Bool))))
                          else (pure false)) && ((__SCTLR_EL2_UCI == 0#1) : Bool))) ) : SailM Bool )
                  if (w__31 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__32 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_DC w__32 CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoDP))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__34 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TPCP == 1#1) : Bool))) ) : SailM Bool )
          if (w__34 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__39 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_DCCVADP == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__39 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__40 CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoDP))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__41 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_DC w__41 CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoDP))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__42 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__42 CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoDP))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DC_CGDVAP_SysOpsWrite_341059a5c0ebf49f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_UCI : (BitVec 1) := (_get_SCTLR_EL1_Type_UCI w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TPCP : (BitVec 1) := (_get_HCR_EL2_Type_TPCP w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_DCCVAP : (BitVec 1) := (_get_HFGITR_EL2_Type_DCCVAP w__5)
  let w__6 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let __SCTLR_EL2_UCI : (BitVec 1) := (_get_SCTLR_EL2_Type_UCI w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__11 ← (( do
        (pure ((← do
              let w__10 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_E2H w__8) +++ (_get_HCR_EL2_Type_TGE w__9)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              (pure (((! w__10) : Bool)))) && ((__SCTLR_EL1_UCI == 0#1) : Bool))) ) : SailM Bool )
      if (w__11 : Bool)
      then
        (do
          let w__13 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else
        (do
          let w__18 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_E2H w__15) +++ (_get_HCR_EL2_Type_TGE w__16)) != 0b11#2) : Bool))))
                  else (pure false)) && ((__HCR_EL2_TPCP == 1#1) : Bool))) ) : SailM Bool )
          if (w__18 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__26 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     let w__20 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     let w__21 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     (pure (((((_get_HCR_EL2_Type_E2H w__20) +++ (_get_HCR_EL2_Type_TGE
                                             w__21)) != 0b11#2) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_DCCVAP == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__26 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__31 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__29 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__28) +++ (_get_HCR_EL2_Type_TGE
                                      w__29)) == 0b11#2) : Bool))))
                          else (pure false)) && ((__SCTLR_EL2_UCI == 0#1) : Bool))) ) : SailM Bool )
                  if (w__31 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__32 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_DC w__32 CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoP))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__34 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TPCP == 1#1) : Bool))) ) : SailM Bool )
          if (w__34 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__39 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_DCCVAP == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__39 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__40 CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoP))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__41 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_DC w__41 CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoP))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__42 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_DC w__42 CacheType_Data_Tag CacheOp_Clean CacheOpScope_PoP))
              else (pure (())))))


end ArmFull.Functions
