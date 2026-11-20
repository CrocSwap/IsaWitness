module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0019
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0039
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0097
public import ArmFull.Fn.M0113
public import ArmFull.Fn.M0115
public import ArmFull.Fn.M0116
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0152
public import ArmFull.Fn.M0153
public import ArmFull.Fn.M0168
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0187 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: k_is_instr : Bool -/
def EffectiveMTX (address : (BitVec 64)) (is_instr : Bool) (el : (BitVec 2)) : SailM (BitVec 1) := do
  let mtx ← (( do (undefined_bitvector_at (← occLabel 741) 1) ) : SailM (BitVec 1) )
  let w__0 ← (( do (HaveEL el) ) : SailM Bool )
  ArmFull.assert w__0 "sail-inputs/03-v8_base.sail:11122.21-11122.22"
  let regime ← (( do (S1TranslationRegime el) ) : SailM (BitVec 2) )
  let w__1 ← (( do (ELUsingAArch32 regime) ) : SailM Bool )
  ArmFull.assert (! w__1) "sail-inputs/03-v8_base.sail:11124.43-11124.44"
  let w__3 ← (( do
    (pure ((← do
          let w__2 ← (( do (HaveMTE4Ext ()) ) : SailM Bool )
          (pure (((! w__2) : Bool)))) || (is_instr : Bool))) ) : SailM Bool )
  if (w__3 : Bool)
  then (pure (0#1))
  else
    (do
      let questionMark := regime
      if ((questionMark == EL1) : Bool)
      then
        (do
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access address 55)])) == 1#1) : Bool)
          then
            (do
              let w__4 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_MTX1 w__4))))
          else
            (do
              let w__5 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_TCR_EL1_Type_MTX0 w__5)))))
      else
        (do
          if ((questionMark == EL2) : Bool)
          then
            (do
              let w__9 ← (( do
                if ((← do
                     (HaveVirtHostExt ())) : Bool)
                then
                  (do
                    (ELIsInHost el))
                else (pure false) ) : SailM Bool )
              if (w__9 : Bool)
              then
                (do
                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access address 55)])) == 1#1) : Bool)
                  then
                    (do
                      let w__10 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                      (pure ((_get_TCR_EL2_Type_MTX1 w__10))))
                  else
                    (do
                      let w__11 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                      (pure ((_get_TCR_EL2_Type_MTX0 w__11)))))
              else
                (do
                  let w__13 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                  let mtx := ((_get_TCR_EL2_Type_MTX w__13) : (BitVec 1))
                  (pure (mtx))))
          else
            (do
              if ((questionMark == EL3) : Bool)
              then
                (do
                  let w__14 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
                  let mtx := ((_get_TCR_EL3_Type_MTX w__14) : (BitVec 1))
                  (pure (mtx)))
              else (pure (mtx)))))


def AltPARTIDspace (el : (BitVec 2)) (security : SecurityState) (primaryPIdSpace : PARTIDspaceType) : SailM PARTIDspaceType := do
  match security with
  | .SS_NonSecure =>
    (do
      ArmFull.assert (el != EL3) "sail-inputs/03-v8_base.sail:11347.26-11347.27"
      (pure (primaryPIdSpace)))
  | .SS_Secure =>
    (do
      ArmFull.assert (el != EL3) "sail-inputs/03-v8_base.sail:11351.26-11351.27"
      if ((BEq.beq primaryPIdSpace PIdSpace_NonSecure) : Bool)
      then (pure (primaryPIdSpace))
      else
        (do
          (AltPIdSecure el primaryPIdSpace)))
  | .SS_Root =>
    (do
      ArmFull.assert (el == EL3) "sail-inputs/03-v8_base.sail:11358.26-11358.27"
      let w__2 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
      if (((_get_MPAM3_EL3_Type_ALTSP_EL3 w__2) == 1#1) : Bool)
      then
        (do
          let w__3 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
          let w__4 : PARTIDspaceType :=
            if (((_get_MPAM3_EL3_Type_RT_ALTSP_NS w__3) == 1#1) : Bool)
            then PIdSpace_NonSecure
            else PIdSpace_Secure
          (pure (w__4)))
      else (pure (primaryPIdSpace)))
  | .SS_Realm =>
    (do
      ArmFull.assert (el != EL3) "sail-inputs/03-v8_base.sail:11370.26-11370.27"
      (AltPIdRealm el primaryPIdSpace))


/-- Type quantifiers: k_InD : Bool, k_InSM : Bool -/
def genMPAM (el : (BitVec 2)) (InD : Bool) (InSM : Bool) (pspace : PARTIDspaceType) : SailM MPAMinfo := do
  let returninfo ← (( do (undefined_MPAMinfo (← occLabel 765) ()) ) : SailM MPAMinfo )
  let partidel ← (( do (undefined_bitvector_at (← occLabel 766) 16) ) : SailM PARTIDtype )
  let perr ← (( do (undefined_bool_at (← occLabel 767) ()) ) : SailM Bool )
  let gstplk ← (( do
    if ((← do
         if ((← do
              if (((el == EL0) : Bool) : Bool)
              then
                (do
                  (EL2Enabled ()))
              else (pure false)) : Bool)
         then
           (do
             let w__2 ← (( do readReg MPAMHCR_EL2 ) : SailM (BitVec 64) )
             (pure ((((_get_MPAMHCR_EL2_Type_GSTAPP_PLK w__2) == 1#1) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_TGE w__4) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let eff_el : (BitVec 2) :=
    if (gstplk : Bool)
    then EL1
    else el
  let w__5 ← (( do (genPARTID eff_el InD InSM) ) : SailM ((BitVec 16) × Bool) )
  let (tup__0, tup__1) := (w__5 : ((BitVec 16) × Bool))
  let partidel : PARTIDtype := tup__0
  let perr : Bool := tup__1
  let groupel ← (( do (genPMG eff_el InD InSM perr) ) : SailM PMGtype )
  let returninfo : MPAMinfo := { returninfo with mpam_sp := pspace }
  let returninfo : MPAMinfo := { returninfo with partid := partidel }
  let returninfo : MPAMinfo := { returninfo with pmg := groupel }
  (pure (returninfo))


def TranslationRegime (el : (BitVec 2)) : SailM Regime := do
  if ((el == EL3) : Bool)
  then
    (do
      let w__0 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
      let w__1 : Regime :=
        if (w__0 : Bool)
        then Regime_EL30
        else Regime_EL3
      (pure (w__1)))
  else
    (do
      if ((el == EL2) : Bool)
      then
        (do
          let w__2 ← (( do (ELIsInHost EL2) ) : SailM Bool )
          let w__3 : Regime :=
            if (w__2 : Bool)
            then Regime_EL20
            else Regime_EL2
          (pure (w__3)))
      else
        (do
          if ((el == EL1) : Bool)
          then (pure (Regime_EL10))
          else
            (do
              if ((el == EL0) : Bool)
              then
                (do
                  let w__6 ← (( do
                    if ((← do
                         let w__4 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
                         (pure (((BEq.beq w__4 SS_Secure) : Bool)))) : Bool)
                    then
                      (do
                        (ELUsingAArch32 EL3))
                    else (pure false) ) : SailM Bool )
                  if (w__6 : Bool)
                  then (pure (Regime_EL30))
                  else
                    (do
                      let w__7 ← (( do (ELIsInHost EL0) ) : SailM Bool )
                      let w__8 : Regime :=
                        if (w__7 : Bool)
                        then Regime_EL20
                        else Regime_EL10
                      (pure (w__8))))
              else
                (do
                  (Unreachable ())
                  (undefined_Regime (← occLabel 770) ())))))


def TTBCR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_TTBCR_Type (← occLabel 799) ()) ) : SailM TTBCR_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      readReg TTBCR_S)
  else
    (do
      (TTBCR_NS_read ()))


def CONTEXTIDR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_CONTEXTIDR_Type (← occLabel 801) ()) ) : SailM CONTEXTIDR_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      readReg CONTEXTIDR_S)
  else
    (do
      (CONTEXTIDR_NS_read ()))


def TTBR0_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do (undefined_TTBR0_Type (← occLabel 803) ()) ) : SailM TTBR0_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      readReg TTBR0_S)
  else
    (do
      readReg TTBR0_NS)


def TTBR1_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do (undefined_TTBR1_Type (← occLabel 808) ()) ) : SailM TTBR1_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      readReg TTBR1_S)
  else
    (do
      readReg TTBR1_NS)


/-- Type quantifiers: n : Int -/
def Rmode_set (n : Int) (mode : (BitVec 5)) (value_name : (BitVec 32)) : SailM Unit := do
  ArmFull.assert ((n ≥b 0) && (n ≤b 14)) "sail-inputs/03-v8_base.sail:13993.27-13993.28"
  let w__0 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
  if ((bne w__0 SS_Secure) : Bool)
  then
    (do
      ArmFull.assert (mode != M32_Monitor) "sail-inputs/03-v8_base.sail:13995.34-13995.35")
  else (pure (()))
  let w__1 ← (( do (BadMode mode) ) : SailM Bool )
  ArmFull.assert (! w__1) "sail-inputs/03-v8_base.sail:13997.34-13997.35"
  if ((mode == M32_Monitor) : Bool)
  then
    (do
      if ((n == 13) : Bool)
      then
        (do
          writeReg SP_mon value_name)
      else
        (do
          if ((n == 14) : Bool)
          then
            (do
              writeReg LR_mon value_name)
          else
            (do
              (set_R_bits (Sail.Int.toNatChecked (n)) 31 0 value_name))))
  else
    (do
      let w__4 ← (( do
        if ((← do
             (HaveAArch64 ())) : Bool)
        then
          (do
            (ConstrainUnpredictableBool Unpredictable_ZEROUPPER))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__5 ← (( do (LookUpRIndex (Sail.Int.toNatChecked (n)) mode) ) : SailM Int )
          (set_R (Sail.Int.toNatChecked (w__5)) (Sail.BitVec.zeroExtend value_name 64)))
      else
        (do
          let w__6 ← (( do (LookUpRIndex (Sail.Int.toNatChecked (n)) mode) ) : SailM Int )
          (set_R_bits (Sail.Int.toNatChecked (w__6)) 31 0 value_name)))


def DFAR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DFAR_Type := value_name
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (DFAR_S_write r))
  else
    (do
      (DFAR_NS_write r))


def DFSR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DFSR_Type := value_name
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      writeReg DFSR_S r)
  else
    (do
      (DFSR_NS_write r))


def IFSR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : IFSR_Type := value_name
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      writeReg IFSR_S r)
  else
    (do
      (IFSR_NS_write r))


def IFAR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : IFAR_Type := value_name
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (IFAR_S_write r))
  else
    (do
      (IFAR_NS_write r))


/-- Type quantifiers: k_d_side : Bool, k_pavalid : Bool -/
def AArch64_FaultSyndrome (d_side : Bool) (fault : FaultRecord) (pavalid : Bool) : SailM ((BitVec 25) × (BitVec 24)) := do
  ArmFull.assert (bne fault.statuscode Fault_None) "sail-inputs/03-v8_base.sail:14749.41-14749.42"
  let iss : (BitVec 25) := (Zeros (n := 25))
  let iss2 : (BitVec 24) := (Zeros (n := 24))
  let w__1 ← (( do
    (pure ((← do
          (HaveRASExt ())) && ((BEq.beq fault.statuscode Fault_SyncExternal) : Bool))) ) : SailM
    Bool )
  let iss ← (( do
    if (w__1 : Bool)
    then
      (do
        let errstate ← (( do (AArch64_PEErrorState fault) ) : SailM ErrorState )
        let w__2 ← (( do (AArch64_EncodeSyncErrorSyndrome errstate) ) : SailM (BitVec 2) )
        let iss := ((Sail.BitVec.updateSubrange iss 12 11 w__2) : (BitVec 25))
        (pure (iss)))
    else (pure (iss)) ) : SailM (BitVec 25) )
  let (iss, iss2) ← (( do
    if (d_side : Bool)
    then
      (do
        let iss2 : (BitVec 24) :=
          if ((BEq.beq fault.access.acctype AccessType_GCS) : Bool)
          then (BitVec.update iss2 8 (Bit 1#1))
          else iss2
        let w__4 ← (( do
          (pure ((← do
                (HaveFeatLS64 ())) && (fault.access.ls64 : Bool))) ) : SailM Bool )
        let (iss, iss2) ← (( do
          if (w__4 : Bool)
          then
            (do
              if (((BEq.beq fault.statuscode Fault_AccessFlag) || ((BEq.beq fault.statuscode
                       Fault_Translation) || (BEq.beq fault.statuscode Fault_Permission))) : Bool)
              then
                (do
                  let w__5 ← (( do (LS64InstructionSyndrome ()) ) : SailM
                    ((BitVec 24) × (BitVec 11)) )
                  let (tup__0, tup__1) := (w__5 : ((BitVec 24) × (BitVec 11)))
                  let iss2 : (BitVec 24) := tup__0
                  let iss : (BitVec 25) := (Sail.BitVec.updateSubrange iss 24 14 tup__1)
                  (pure ((iss, iss2))))
              else (pure ((iss, iss2))))
          else
            (do
              let w__14 ← (( do
                if ((← do
                     (pure ((← do
                           (IsSecondStage fault)) && ((! fault.s2fs1walk) : Bool)))) : Bool)
                then
                  (do
                    if ((← do
                         let w__8 ← (( do (IsExternalSyncAbort__1 fault) ) : SailM Bool )
                         (pure (((! w__8) : Bool)))) : Bool)
                    then (pure true)
                    else
                      (do
                        if ((← do
                             (pure ((← do
                                   let w__9 ← (( do (HaveRASExt ()) ) : SailM Bool )
                                   (pure (((! w__9) : Bool)))) && ((BEq.beq fault.access.acctype
                                   AccessType_TTW) : Bool)))) : Bool)
                        then
                          (do
                            (__IMPDEF_boolean "ISV on second stage translation table walk"))
                        else (pure false)))
                else (pure false) ) : SailM Bool )
              let iss : (BitVec 25) :=
                if (w__14 : Bool)
                then (Sail.BitVec.updateSubrange iss 24 14 (LSInstructionSyndrome ()))
                else iss
              (pure ((iss, iss2)))) ) : SailM ((BitVec 25) × (BitVec 24)) )
        let w__16 ← (( do
          (pure ((← do
                (HaveNV2Ext ())) && ((BEq.beq fault.access.acctype AccessType_NV2) : Bool))) ) :
          SailM Bool )
        let iss : (BitVec 25) :=
          if (w__16 : Bool)
          then (BitVec.update iss 13 (Bit 1#1))
          else iss
        let w__18 ← (( do
          (pure ((← do
                (HaveFeatLS64 ())) && (((BEq.beq fault.statuscode Fault_AccessFlag) || ((BEq.beq
                    fault.statuscode Fault_Translation) || (BEq.beq fault.statuscode
                    Fault_Permission))) : Bool))) ) : SailM Bool )
        let iss ← (( do
          if (w__18 : Bool)
          then
            (do
              let w__19 ← (( do (GetLoadStoreType ()) ) : SailM (BitVec 2) )
              let iss := ((Sail.BitVec.updateSubrange iss 12 11 w__19) : (BitVec 25))
              (pure (iss)))
          else (pure (iss)) ) : SailM (BitVec 25) )
        let iss : (BitVec 25) :=
          if (((BEq.beq fault.access.acctype AccessType_DC) || ((BEq.beq fault.access.acctype
                   AccessType_IC) || (BEq.beq fault.access.acctype AccessType_AT))) : Bool)
          then (BitVec.update iss 8 (Bit 1#1))
          else iss
        let iss ← (( do
          if (((BEq.beq fault.access.acctype AccessType_DC) || ((BEq.beq fault.access.acctype
                   AccessType_IC) || (BEq.beq fault.access.acctype AccessType_AT))) : Bool)
          then
            (let iss : (BitVec 25) := (BitVec.update iss 6 (Bit 1#1))
            (pure (iss)))
          else
            (do
              if (((BEq.beq fault.statuscode Fault_HWUpdateAccessFlag) || (BEq.beq fault.statuscode
                     Fault_Exclusive)) : Bool)
              then
                (do
                  let w__20 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
                  let iss := ((BitVec.update iss 6 (Bit w__20)) : (BitVec 25))
                  (pure (iss)))
              else
                (do
                  let w__22 ← (( do
                    if ((fault.access.atomicop : Bool) : Bool)
                    then
                      (do
                        (IsExternalAbort__1 fault))
                    else (pure false) ) : SailM Bool )
                  if (w__22 : Bool)
                  then
                    (do
                      let w__23 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
                      let iss := ((BitVec.update iss 6 (Bit w__23)) : (BitVec 25))
                      (pure (iss)))
                  else
                    (let iss : (BitVec 25) :=
                      (BitVec.update iss 6
                        (Bit
                          (if (fault.write : Bool)
                          then 1#1
                          else 0#1)))
                    (pure (iss))))) ) : SailM (BitVec 25) )
        let (iss, iss2) : ((BitVec 25) × (BitVec 24)) :=
          if ((BEq.beq fault.statuscode Fault_Permission) : Bool)
          then
            (let iss2 : (BitVec 24) :=
              (BitVec.update iss2 5
                (Bit
                  (if (fault.dirtybit : Bool)
                  then 1#1
                  else 0#1)))
            let iss2 : (BitVec 24) :=
              (BitVec.update iss2 6
                (Bit
                  (if (fault.overlay : Bool)
                  then 1#1
                  else 0#1)))
            let iss : (BitVec 25) :=
              if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access iss 24)])) == 0#1) : Bool)
              then
                (BitVec.update iss 21
                  (Bit
                    (if (fault.toplevel : Bool)
                    then 1#1
                    else 0#1)))
              else iss
            let iss2 : (BitVec 24) :=
              (BitVec.update iss2 7
                (Bit
                  (if (fault.assuredonly : Bool)
                  then 1#1
                  else 0#1)))
            let iss2 : (BitVec 24) :=
              (BitVec.update iss2 9
                (Bit
                  (if (fault.tagaccess : Bool)
                  then 1#1
                  else 0#1)))
            let iss2 : (BitVec 24) :=
              (BitVec.update iss2 10
                (Bit
                  (if (fault.s1tagnotdata : Bool)
                  then 1#1
                  else 0#1)))
            (iss, iss2))
          else (iss, iss2)
        (pure ((iss, iss2))))
    else
      (let (iss, iss2) : ((BitVec 25) × (BitVec 24)) :=
        if (((BEq.beq fault.access.acctype AccessType_IFETCH) && (BEq.beq fault.statuscode
               Fault_Permission)) : Bool)
        then
          (let iss2 : (BitVec 24) :=
            (BitVec.update iss2 5
              (Bit
                (if (fault.dirtybit : Bool)
                then 1#1
                else 0#1)))
          let iss : (BitVec 25) :=
            (BitVec.update iss 21
              (Bit
                (if (fault.toplevel : Bool)
                then 1#1
                else 0#1)))
          let iss2 : (BitVec 24) :=
            (BitVec.update iss2 7
              (Bit
                (if (fault.assuredonly : Bool)
                then 1#1
                else 0#1)))
          let iss2 : (BitVec 24) :=
            (BitVec.update iss2 6
              (Bit
                (if (fault.overlay : Bool)
                then 1#1
                else 0#1)))
          (iss, iss2))
        else (iss, iss2)
      (pure ((iss, iss2)))) ) : SailM ((BitVec 25) × (BitVec 24)) )
  let w__24 ← (( do (IsExternalAbort__1 fault) ) : SailM Bool )
  let iss : (BitVec 25) :=
    if (w__24 : Bool)
    then (BitVec.update iss 9 (Bit fault.extflag))
    else iss
  let iss : (BitVec 25) :=
    (BitVec.update iss 7
      (Bit
        (if (fault.s2fs1walk : Bool)
        then 1#1
        else 0#1)))
  let w__25 ← (( do (EncodeLDFSC fault.statuscode fault.level) ) : SailM (BitVec 6) )
  let iss := ((Sail.BitVec.updateSubrange iss 5 0 w__25) : (BitVec 25))
  (pure ((iss, iss2)))


end ArmFull.Functions
