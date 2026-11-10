import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0019
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0044
import ArmFull.Fn.M0046
import ArmFull.Fn.M0047
import ArmFull.Fn.M0097
import ArmFull.Fn.M0115
import ArmFull.Fn.M0116
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0154
import ArmFull.Fn.M0166
import ArmFull.Fn.M0167
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
import ArmFull.Fn.M0184
import ArmFull.Fn.M0186
import ArmFull.Fn.M0187

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
  ArmFull.assert ((n ≥b 0) && (n ≤b 14)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:13980.27-13980.28"
  let w__0 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
  if ((bne w__0 SS_Secure) : Bool)
  then
    (do
      ArmFull.assert (mode != M32_Monitor) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:13982.34-13982.35")
  else (pure (()))
  let w__1 ← (( do (BadMode mode) ) : SailM Bool )
  ArmFull.assert (! w__1) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:13984.34-13984.35"
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
  ArmFull.assert (bne fault.statuscode Fault_None) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:14736.41-14736.42"
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


def AArch64_RouteToSErrorOffset (target_el : (BitVec 2)) : SailM Bool := do
  let w__0 ← (( do (HaveDoubleFaultExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let ease_bit ← (( do (undefined_bitvector_at (← occLabel 865) 1) ) : SailM (BitVec 1) )
      let questionMark := target_el
      let ease_bit ← (( do
        if ((questionMark == EL3) : Bool)
        then
          (do
            let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            let ease_bit := ((_get_SCR_EL3_Type_EASE w__1) : (BitVec 1))
            (pure (ease_bit)))
        else
          (do
            if ((questionMark == EL2) : Bool)
            then
              (do
                let w__4 ← (( do
                  if ((← do
                       (HaveDoubleFault2Ext ())) : Bool)
                  then
                    (do
                      (IsSCTLR2EL2Enabled ()))
                  else (pure false) ) : SailM Bool )
                if (w__4 : Bool)
                then
                  (do
                    let w__5 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
                    let ease_bit := ((_get_SCTLR2_EL2_Type_EASE w__5) : (BitVec 1))
                    (pure (ease_bit)))
                else (pure (0#1)))
            else
              (do
                if ((questionMark == EL1) : Bool)
                then
                  (do
                    let w__8 ← (( do
                      if ((← do
                           (HaveDoubleFault2Ext ())) : Bool)
                      then
                        (do
                          (IsSCTLR2EL1Enabled ()))
                      else (pure false) ) : SailM Bool )
                    if (w__8 : Bool)
                    then
                      (do
                        let w__9 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
                        let ease_bit := ((_get_SCTLR2_EL1_Type_EASE w__9) : (BitVec 1))
                        (pure (ease_bit)))
                    else (pure (0#1)))
                else (pure (ease_bit)))) ) : SailM (BitVec 1) )
      (pure ((ease_bit == 1#1))))


def AArch64_SyncExternalAbortTarget (fault : FaultRecord) : SailM (BitVec 2) := do
  let route_to_el3 ← (( do (undefined_bool_at (← occLabel 866) ()) ) : SailM Bool )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let route_to_el3 ← (( do
    if ((w__0.EL != EL3) : Bool)
    then
      (do
        if (((HaveEL EL3) : Bool) : Bool)
        then
          (do
            let w__1 ← (( do (EffectiveEA ()) ) : SailM (BitVec 1) )
            (pure (((w__1 == 1#1) : Bool))))
        else (pure false))
    else (pure (false)) ) : SailM Bool )
  let w__3 ← (( do (HaveRASExt ()) ) : SailM Bool )
  let tea_bit ← (( do
    if (w__3 : Bool)
    then
      (do
        let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_HCR_EL2_Type_TEA w__4))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let route_to_el2 ← (( do (undefined_bool_at (← occLabel 867) ()) ) : SailM Bool )
  let w__8 ← (( do
    if ((← do
         if (((! route_to_el3) : Bool) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__7.EL == EL1) : Bool))))
    else (pure false) ) : SailM Bool )
  let route_to_el2 ← (( do
    if (w__8 : Bool)
    then
      (do
        if ((((tea_bit == 1#1) || (BEq.beq fault.access.acctype AccessType_NV2)) : Bool) : Bool)
        then (pure true)
        else
          (do
            (IsSecondStage fault)))
    else
      (do
        let w__14 ← (( do
          if ((← do
               if (((! route_to_el3) : Bool) : Bool)
               then
                 (do
                   (EL2Enabled ()))
               else (pure false)) : Bool)
          then
            (do
              let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__13.EL == EL0) : Bool))))
          else (pure false) ) : SailM Bool )
        if (w__14 : Bool)
        then
          (do
            if ((← do
                 let w__15 ← (( do (IsInHost ()) ) : SailM Bool )
                 (pure (((! w__15) : Bool)))) : Bool)
            then
              (do
                if ((← do
                     (pure ((← do
                           let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                           (pure ((((_get_HCR_EL2_Type_TGE w__16) == 1#1) : Bool)))) || ((tea_bit == 1#1) : Bool)))) : Bool)
                then (pure true)
                else
                  (do
                    (IsSecondStage fault)))
            else (pure false))
        else (pure (false))) ) : SailM Bool )
  let route_masked_to_el3 ← (( do (undefined_bool_at (← occLabel 868) ()) ) : SailM Bool )
  let route_masked_to_el2 ← (( do (undefined_bool_at (← occLabel 869) ()) ) : SailM Bool )
  let w__21 ← (( do (HaveDoubleFault2Ext ()) ) : SailM Bool )
  let (route_masked_to_el2, route_masked_to_el3) ← (( do
    if (w__21 : Bool)
    then
      (do
        let w__31 ← (( do
          if ((← do
               if ((← do
                    if ((← do
                         (pure ((← do
                               (EL2Enabled ())) && ((! route_to_el3) : Bool)))) : Bool)
                    then
                      (do
                        if ((← do
                             let w__24 ← (( do readReg PSTATE ) : SailM ProcState )
                             (pure (((w__24.EL == EL1) : Bool)))) : Bool)
                        then
                          (do
                            let w__25 ← (( do readReg PSTATE ) : SailM ProcState )
                            (pure (((w__25.A == 1#1) : Bool))))
                        else (pure false))
                    else (pure false)) : Bool)
               then
                 (do
                   (IsHCRXEL2Enabled ()))
               else (pure false)) : Bool)
          then
            (do
              let w__30 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_HCRX_EL2_Type_TMEA w__30) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let route_masked_to_el2 := (w__31 : Bool)
        let w__39 ← (( do
          if ((← do
               if ((((HaveEL EL3) && (! (route_to_el2 || route_masked_to_el2))) : Bool) : Bool)
               then
                 (do
                   if ((← do
                        if ((← do
                             let w__32 ← (( do readReg PSTATE ) : SailM ProcState )
                             (pure (((w__32.EL == EL2) : Bool)))) : Bool)
                        then (pure true)
                        else
                          (do
                            let w__33 ← (( do readReg PSTATE ) : SailM ProcState )
                            (pure (((w__33.EL == EL1) : Bool))))) : Bool)
                   then
                     (do
                       let w__35 ← (( do readReg PSTATE ) : SailM ProcState )
                       (pure (((w__35.A == 1#1) : Bool))))
                   else (pure false))
               else (pure false)) : Bool)
          then
            (do
              let w__38 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
              (pure ((((_get_SCR_EL3_Type_TMEA w__38) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let route_masked_to_el3 := (w__39 : Bool)
        (pure ((route_masked_to_el2, route_masked_to_el3))))
    else
      (let route_masked_to_el2 : Bool := false
      let route_masked_to_el3 : Bool := false
      (pure ((route_masked_to_el2, route_masked_to_el3)))) ) : SailM (Bool × Bool) )
  let w__40 ← (( do readReg PSTATE ) : SailM ProcState )
  let take_in_el3 : Bool := (w__40.EL == EL3)
  let take_in_el2_0 ← (( do
    (pure ((← do
          if ((← do
               let w__41 ← (( do readReg PSTATE ) : SailM ProcState )
               (pure (((w__41.EL == EL2) : Bool)))) : Bool)
          then (pure true)
          else
            (do
              (IsInHost ()))) && ((! (route_to_el3 || route_masked_to_el3)) : Bool))) ) : SailM Bool
    )
  let take_in_el1_0 ← (( do
    (pure ((← do
          (pure ((← do
                if ((← do
                     let w__44 ← (( do readReg PSTATE ) : SailM ProcState )
                     (pure (((w__44.EL == EL1) : Bool)))) : Bool)
                then (pure true)
                else
                  (do
                    if ((← do
                         let w__45 ← (( do readReg PSTATE ) : SailM ProcState )
                         (pure (((w__45.EL == EL0) : Bool)))) : Bool)
                    then
                      (do
                        let w__46 ← (( do (IsInHost ()) ) : SailM Bool )
                        (pure (((! w__46) : Bool))))
                    else (pure false))) && ((! (route_to_el2 || route_masked_to_el2)) : Bool)))) && ((! (route_to_el3 || route_masked_to_el3)) : Bool)))
    ) : SailM Bool )
  let target_el ← (( do (undefined_bitvector_at (← occLabel 870) 2) ) : SailM (BitVec 2) )
  if (((take_in_el3 || route_to_el3) || route_masked_to_el3) : Bool)
  then (pure (EL3))
  else
    (do
      if (((take_in_el2_0 || route_to_el2) || route_masked_to_el2) : Bool)
      then (pure (EL2))
      else
        (do
          if (take_in_el1_0 : Bool)
          then (pure (EL1))
          else
            (do
              ArmFull.assert false "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:14970.20-14970.21"
              throw Error.Exit)))


end ArmFull.Functions
