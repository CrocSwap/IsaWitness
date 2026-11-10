import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0042
import ArmFull.Fn.M0049
import ArmFull.Fn.M0051
import ArmFull.Fn.M0087
import ArmFull.Fn.M0097
import ArmFull.Fn.M0117
import ArmFull.Fn.M0120
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0152
import ArmFull.Fn.M0154
import ArmFull.Fn.M0155
import ArmFull.Fn.M0156
import ArmFull.Fn.M0166
import ArmFull.Fn.M0167
import ArmFull.Fn.M0171
import ArmFull.Fn.M0172
import ArmFull.Fn.M0179
import ArmFull.Fn.M0181
import ArmFull.Fn.M0182
import ArmFull.Fn.M0185
import ArmFull.Fn.M0203
import ArmFull.Fn.M0204
import ArmFull.Fn.M0237
import ArmFull.Fn.M0247
import ArmFull.Fn.M0248
import ArmFull.Fn.M0249

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

def AArch32_TakeUndefInstrException__1 (except : ExceptionRecord) : SailM Unit := do
  let route_to_hyp ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__0.EL == EL0) : Bool)))) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__3 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
        (pure ((((_get_HCR_Type_TGE w__3) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let preferred_exception_return ← (( do (ThisInstrAddr 32) ) : SailM (BitVec 32) )
  let vect_offset : Int := (BitVec.toNat 0x04#8)
  let w__4 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
  let lr_offset : Int :=
    if ((BEq.beq w__4 InstrSet_A32) : Bool)
    then 4
    else 2
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__5.EL == EL2) : Bool)
  then
    (do
      (AArch32_EnterHypMode except preferred_exception_return vect_offset))
  else
    (do
      if (route_to_hyp : Bool)
      then
        (do
          (AArch32_EnterHypMode except preferred_exception_return (BitVec.toNat 0x14#8)))
      else
        (do
          (AArch32_EnterMode M32_Undef preferred_exception_return lr_offset vect_offset)))


/-- Type quantifiers: k_is_ase : Bool -/
def AArch64_FPTrappedException (is_ase : Bool) (accumulated_exceptions : (BitVec 8)) : SailM Unit := do
  let except ← (( do (ExceptionSyndrome Exception_FPTrappedException) ) : SailM ExceptionRecord )
  let except ← (( do
    if (is_ase : Bool)
    then
      (do
        let w__0 ← (( do (__IMPDEF_boolean "vector instructions set TFV to 1") ) : SailM Bool )
        let except : ExceptionRecord :=
          if (w__0 : Bool)
          then { except with syndrome := (BitVec.update except.syndrome 23 (Bit 1#1)) }
          else { except with syndrome := (BitVec.update except.syndrome 23 (Bit 0#1)) }
        (pure (except)))
    else
      (let except : ExceptionRecord :=
        { except with syndrome := (BitVec.update except.syndrome 23 (Bit 1#1)) }
      (pure (except))) ) : SailM ExceptionRecord )
  let w__1 ← (( do (__UNKNOWN_bits 3) ) : SailM (BitVec 3) )
  let except :=
    ({ except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 10 8 w__1) } : ExceptionRecord)
  let except ← (( do
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access except.syndrome 23)])) == 1#1) : Bool)
    then
      (let split_vec :=
        ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access accumulated_exceptions 7)])) +++ (Sail.BitVec.extractLsb
            accumulated_exceptions 4 0))
      let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 7 7
            (Sail.BitVec.extractLsb split_vec 5 5)) }
      let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 4 0
            (Sail.BitVec.extractLsb split_vec 4 0)) }
      (pure (except)))
    else
      (do
        let split_vec ← (( do (__UNKNOWN_bits 6) ) : SailM (BitVec 6) )
        let except : ExceptionRecord :=
          { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 7 7
              (Sail.BitVec.extractLsb split_vec 5 5)) }
        let except : ExceptionRecord :=
          { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 4 0
              (Sail.BitVec.extractLsb split_vec 4 0)) }
        (pure (except))) ) : SailM ExceptionRecord )
  let route_to_el2 ← (( do
    if ((← do
         (EL2Enabled ())) : Bool)
    then
      (do
        let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_TGE w__3) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  if (((BitVec.toNat w__4.EL) >b (BitVec.toNat EL1)) : Bool)
  then
    (do
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      (AArch64_TakeException w__5.EL except preferred_exception_return vect_offset))
  else
    (do
      if (route_to_el2 : Bool)
      then
        (do
          (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
      else
        (do
          (AArch64_TakeException EL1 except preferred_exception_return vect_offset)))


def AArch64_PACFailException (syndrome : (BitVec 2)) : SailM Unit := do
  let route_to_el2 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__0.EL == EL0) : Bool)))) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_TGE w__3) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_PACFail) ) : SailM ExceptionRecord )
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 1 0 syndrome) }
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 24 2 (Zeros (n := 23))) }
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  if (((BitVec.toNat w__4.EL) >b (BitVec.toNat EL0)) : Bool)
  then
    (do
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      (AArch64_TakeException w__5.EL except preferred_exception_return vect_offset))
  else
    (do
      if (route_to_el2 : Bool)
      then
        (do
          (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
      else
        (do
          (AArch64_TakeException EL1 except preferred_exception_return vect_offset)))


def TrapPACUse (target_el : (BitVec 2)) : SailM Unit := do
  let w__1 ← (( do
    if ((((HaveEL target_el) && (target_el != EL0)) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure ((((BitVec.toNat target_el) ≥b (BitVec.toNat w__0.EL)) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__1 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:21695.86-21695.87"
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Nat := 0
  let except ← (( do (ExceptionSyndrome Exception_PACTrap) ) : SailM ExceptionRecord )
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)


def AArch64_SPAlignmentFault (_ : Unit) : SailM Unit := do
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_SPAlignment) ) : SailM ExceptionRecord )
  let target_el : (BitVec 2) := EL1
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let target_el ← (( do
    if (((BitVec.toNat w__0.EL) >b (BitVec.toNat EL1)) : Bool)
    then
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        let target_el := (w__1.EL : (BitVec 2))
        (pure (target_el)))
    else
      (do
        let w__4 ← (( do
          if ((← do
               (EL2Enabled ())) : Bool)
          then
            (do
              let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_HCR_EL2_Type_TGE w__3) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let target_el : (BitVec 2) :=
          if (w__4 : Bool)
          then EL2
          else target_el
        (pure (target_el))) ) : SailM (BitVec 2) )
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)


def AArch64_RaiseTagCheckFault (va : (BitVec 64)) (fault : FaultRecord) : SailM Unit := do
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let target_el : (BitVec 2) := EL1
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let target_el ← (( do
    if (((BitVec.toNat w__0.EL) >b (BitVec.toNat EL1)) : Bool)
    then
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        let target_el := (w__1.EL : (BitVec 2))
        (pure (target_el)))
    else
      (do
        let w__6 ← (( do
          if ((← do
               if ((← do
                    let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__2.EL == EL0) : Bool)))) : Bool)
               then
                 (do
                   (EL2Enabled ()))
               else (pure false)) : Bool)
          then
            (do
              let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_HCR_EL2_Type_TGE w__5) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let target_el : (BitVec 2) :=
          if (w__6 : Bool)
          then EL2
          else target_el
        (pure (target_el))) ) : SailM (BitVec 2) )
  let except ← (( do (AArch64_AbortSyndrome Exception_DataAbort fault va target_el) ) : SailM
    ExceptionRecord )
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)


/-- Type quantifiers: k_aligned : Bool, k_s1aarch64 : Bool -/
def AArch64_S2Translate (fault_in : FaultRecord) (ipa : AddressDescriptor) (s1aarch64 : Bool) (s1level : (Option Int)) (aligned : Bool) (accdesc : AccessDescriptor) : SailM (FaultRecord × AddressDescriptor) := SailME.run do
  let walkparams ← (( do (AArch64_GetS2TTWParams accdesc.ss ipa.paddress.paspace s1aarch64) ) :
    SailME (FaultRecord × AddressDescriptor) S2TTWParams )
  let fault : FaultRecord := fault_in
  let s2fs1mro ← (( do (undefined_bool_at (← occLabel 1582) ()) ) : SailME
    (FaultRecord × AddressDescriptor) Bool )
  let fault : FaultRecord := { fault with statuscode := Fault_None }
  let fault : FaultRecord := { fault with secondstage := true }
  let fault : FaultRecord := { fault with s2fs1walk := (BEq.beq accdesc.acctype AccessType_TTW) }
  let fault : FaultRecord := { fault with ipaddress := ipa.paddress }
  if ((walkparams.vm != 1#1) : Bool)
  then (pure ((fault, ipa)))
  else
    (do
      let s2mintxsz ← (( do
        (AArch64_S2MinTxSZ walkparams.d128 walkparams.ds walkparams.tgx s1aarch64) ) : SailME
        (FaultRecord × AddressDescriptor) Int )
      let s2maxtxsz ← (( do (AArch64_MaxTxSZ walkparams.tgx) ) : SailME
        (FaultRecord × AddressDescriptor) Int )
      let w__0 ← (( do (AArch64_S2TxSZFaults walkparams s1aarch64) ) : SailME
        (FaultRecord × AddressDescriptor) Bool )
      if (w__0 : Bool)
      then
        (do
          let fault : FaultRecord := { fault with statuscode := Fault_Translation }
          let fault : FaultRecord := { fault with level := 0 }
          let w__1 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
            (FaultRecord × AddressDescriptor) AddressDescriptor )
          (pure ((fault, w__1))))
      else
        (do
          let walkparams : S2TTWParams :=
            if (((BitVec.toNat walkparams.txsz) <b s2mintxsz) : Bool)
            then { walkparams with txsz := (integer_subrange s2mintxsz 5 0) }
            else
              (if (((BitVec.toNat walkparams.txsz) >b s2maxtxsz) : Bool)
              then { walkparams with txsz := (integer_subrange s2maxtxsz 5 0) }
              else walkparams)
          let w__5 ← (( do
            if (((walkparams.d128 == 0#1) : Bool) : Bool)
            then
              (do
                if ((← do
                     (AArch64_S2InvalidSL walkparams)) : Bool)
                then (pure true)
                else
                  (do
                    (AArch64_S2InconsistentSL walkparams)))
            else (pure false) ) : SailME (FaultRecord × AddressDescriptor) Bool )
          if (w__5 : Bool)
          then
            (do
              let fault : FaultRecord := { fault with statuscode := Fault_Translation }
              let fault : FaultRecord := { fault with level := 0 }
              let w__6 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
                (FaultRecord × AddressDescriptor) AddressDescriptor )
              (pure ((fault, w__6))))
          else
            (do
              if ((AArch64_IPAIsOutOfRange ipa.paddress.address walkparams) : Bool)
              then
                (do
                  let fault : FaultRecord := { fault with statuscode := Fault_Translation }
                  let fault : FaultRecord := { fault with level := 0 }
                  let w__7 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
                    (FaultRecord × AddressDescriptor) AddressDescriptor )
                  (pure ((fault, w__7))))
              else
                (do
                  let descpaddr ← (( do (undefined_AddressDescriptor (← occLabel 1583) ()) ) :
                    SailME (FaultRecord × AddressDescriptor) AddressDescriptor )
                  let walkstate ← (( do (undefined_TTWState (← occLabel 1584) ()) ) : SailME
                    (FaultRecord × AddressDescriptor) TTWState )
                  let descriptor ← (( do (undefined_bitvector_at (← occLabel 1585) 128) ) :
                    SailME (FaultRecord × AddressDescriptor) (BitVec 128) )
                  let new_desc ← (( do (undefined_bitvector_at (← occLabel 1586) 128) ) : SailME
                    (FaultRecord × AddressDescriptor) (BitVec 128) )
                  let mem_desc ← (( do (undefined_bitvector_at (← occLabel 1587) 128) ) : SailME
                    (FaultRecord × AddressDescriptor) (BitVec 128) )
                  let (descpaddr, descriptor, fault, mem_desc, new_desc, s2fs1mro, walkstate) ← (( do
                    let loop_vars ← sailUntilFuelM (fuel := 1048576) (fun (descpaddr, descriptor, fault, mem_desc, new_desc, s2fs1mro, walkstate) => (pure ((new_desc == descriptor) || (mem_desc == new_desc)))) (descpaddr, descriptor, fault, mem_desc, new_desc, s2fs1mro, walkstate)
                      fun (descpaddr, descriptor, fault, mem_desc, new_desc, s2fs1mro, walkstate) => do
                        let (descpaddr, descriptor, fault, walkstate) ← (( do
                          if ((walkparams.d128 == 1#1) : Bool)
                          then
                            (do
                              let w__8 ← (( do
                                (AArch64_S2Walk fault ipa walkparams accdesc s1level 128) ) : SailME
                                (FaultRecord × AddressDescriptor)
                                (FaultRecord × AddressDescriptor × TTWState × (BitVec 128)) )
                              let (tup__0, tup__1, tup__2, tup__3) :=
                                (w__8 : (FaultRecord × AddressDescriptor × TTWState × (BitVec 128)))
                              let fault : FaultRecord := tup__0
                              let descpaddr : AddressDescriptor := tup__1
                              let walkstate : TTWState := tup__2
                              let descriptor : (BitVec 128) := tup__3
                              (pure ((descpaddr, descriptor, fault, walkstate))))
                          else
                            (do
                              let w__9 ← (( do
                                (AArch64_S2Walk fault ipa walkparams accdesc s1level 64) ) : SailME
                                (FaultRecord × AddressDescriptor)
                                (FaultRecord × AddressDescriptor × TTWState × (BitVec 64)) )
                              let (tup__0, tup__1, tup__2, tup__3) :=
                                (w__9 : (FaultRecord × AddressDescriptor × TTWState × (BitVec 64)))
                              let fault : FaultRecord := tup__0
                              let descpaddr : AddressDescriptor := tup__1
                              let walkstate : TTWState := tup__2
                              let descriptor : (BitVec 128) :=
                                (Sail.BitVec.updateSubrange descriptor 63 0 tup__3)
                              let descriptor : (BitVec 128) :=
                                (Sail.BitVec.updateSubrange descriptor 127 64 (Zeros (n := 64)))
                              (pure ((descpaddr, descriptor, fault, walkstate)))) ) : SailME
                          (FaultRecord × AddressDescriptor)
                          (AddressDescriptor × (BitVec 128) × FaultRecord × TTWState) )
                        let (fault, mem_desc, new_desc, s2fs1mro) ← (( do
                          if ((bne fault.statuscode Fault_None) : Bool)
                          then
                            (do
                              let w__10 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
                                (FaultRecord × AddressDescriptor) AddressDescriptor )
                              SailME.throw ((fault, w__10) : (FaultRecord × AddressDescriptor))
                              (pure ((fault, mem_desc, new_desc, s2fs1mro))))
                          else
                            (do
                              let w__11 ← (( do
                                (AArch64_S2HasAlignmentFault accdesc aligned walkstate.memattrs) ) :
                                SailME (FaultRecord × AddressDescriptor) Bool )
                              let fault : FaultRecord :=
                                if (w__11 : Bool)
                                then { fault with statuscode := Fault_Alignment }
                                else fault
                              let (fault, s2fs1mro) ← (( do
                                if ((BEq.beq fault.statuscode Fault_None) : Bool)
                                then
                                  (do
                                    let w__12 ← (( do
                                      (AArch64_S2CheckPermissions fault walkstate walkparams ipa
                                        accdesc) ) : SailME (FaultRecord × AddressDescriptor)
                                      (FaultRecord × Bool) )
                                    let (tup__0, tup__1) := (w__12 : (FaultRecord × Bool))
                                    let fault : FaultRecord := tup__0
                                    let s2fs1mro : Bool := tup__1
                                    (pure ((fault, s2fs1mro))))
                                else (pure ((fault, s2fs1mro))) ) : SailME
                                (FaultRecord × AddressDescriptor) (FaultRecord × Bool) )
                              let new_desc : (BitVec 128) := descriptor
                              let w__14 ← (( do
                                if (((walkparams.ha == 1#1) : Bool) : Bool)
                                then
                                  (do
                                    (AArch64_SettingAccessFlagPermitted fault))
                                else (pure false) ) : SailME (FaultRecord × AddressDescriptor) Bool
                                )
                              let new_desc : (BitVec 128) :=
                                if (w__14 : Bool)
                                then (BitVec.update new_desc 10 (Bit 1#1))
                                else new_desc
                              let w__20 ← (( do
                                (pure ((← do
                                      (pure ((← do
                                            (pure ((← do
                                                  (pure ((← do
                                                        (pure ((← do
                                                              (AArch64_SettingDirtyStatePermitted
                                                                fault)) && ((walkparams.ha == 1#1) : Bool)))) && ((walkparams.hd == 1#1) : Bool)))) && (((walkparams.s2pie == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                        descriptor 51)])) == 1#1)) : Bool)))) && (accdesc.write : Bool)))) && ((! ((BEq.beq
                                          accdesc.acctype AccessType_AT) || ((BEq.beq
                                            accdesc.acctype AccessType_IC) || (BEq.beq
                                            accdesc.acctype AccessType_DC)))) : Bool))) ) : SailME
                                (FaultRecord × AddressDescriptor) Bool )
                              let new_desc : (BitVec 128) :=
                                if (w__20 : Bool)
                                then (BitVec.update new_desc 7 (Bit 1#1))
                                else new_desc
                              let (fault, mem_desc) ← (( do
                                if ((new_desc != descriptor) : Bool)
                                then
                                  (do
                                    let descaccess ← (( do (CreateAccDescTTEUpdate accdesc) ) :
                                      SailME (FaultRecord × AddressDescriptor) AccessDescriptor )
                                    let w__21 ← (( do (VMID_read ()) ) : SailME
                                      (FaultRecord × AddressDescriptor) (BitVec 16) )
                                    let translation_info : TranslationInfo :=
                                      { regime := Regime_EL10
                                        vmid := (some w__21)
                                        asid := none
                                        va := ipa.vaddress
                                        s1level := s1level
                                        s2info := (some
                                            ((Sail.BitVec.zeroExtend ipa.paddress.address 64), walkstate.level))
                                        s1params := none
                                        s2params := (some walkparams)
                                        memattrs := walkstate.memattrs }
                                    if ((walkparams.d128 == 1#1) : Bool)
                                    then
                                      (do
                                        let w__22 ← (( do
                                          (AArch64_MemSwapTableDesc fault descriptor new_desc
                                            walkparams.ee descaccess descpaddr translation_info) ) :
                                          SailME (FaultRecord × AddressDescriptor)
                                          (FaultRecord × (BitVec 128)) )
                                        let (tup__0, tup__1) :=
                                          (w__22 : (FaultRecord × (BitVec 128)))
                                        let fault : FaultRecord := tup__0
                                        let mem_desc : (BitVec 128) := tup__1
                                        (pure ((fault, mem_desc))))
                                    else
                                      (do
                                        let w__23 ← (( do
                                          (AArch64_MemSwapTableDesc fault
                                            (Sail.BitVec.extractLsb descriptor 63 0)
                                            (Sail.BitVec.extractLsb new_desc 63 0) walkparams.ee
                                            descaccess descpaddr translation_info) ) : SailME
                                          (FaultRecord × AddressDescriptor)
                                          (FaultRecord × (BitVec 64)) )
                                        let (tup__0, tup__1) :=
                                          (w__23 : (FaultRecord × (BitVec 64)))
                                        let fault : FaultRecord := tup__0
                                        let mem_desc : (BitVec 128) :=
                                          (Sail.BitVec.updateSubrange mem_desc 63 0 tup__1)
                                        let mem_desc : (BitVec 128) :=
                                          (Sail.BitVec.updateSubrange mem_desc 127 64
                                            (Zeros (n := 64)))
                                        (pure ((fault, mem_desc)))))
                                else (pure ((fault, mem_desc))) ) : SailME
                                (FaultRecord × AddressDescriptor) (FaultRecord × (BitVec 128)) )
                              (pure ((fault, mem_desc, new_desc, s2fs1mro)))) ) : SailME
                          (FaultRecord × AddressDescriptor)
                          (FaultRecord × (BitVec 128) × (BitVec 128) × Bool) )
                        (pure ((descpaddr, descriptor, fault, mem_desc, new_desc, s2fs1mro, walkstate)))
                    (pure loop_vars) ) : SailME (FaultRecord × AddressDescriptor)
                    (AddressDescriptor × (BitVec 128) × FaultRecord × (BitVec 128) × (BitVec 128) × Bool × TTWState)
                    )
                  let w__26 ← (( do
                    (pure ((← do
                          (pure ((← do
                                readReg __tlb_enabled) && ((new_desc != descriptor) : Bool)))) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                              mem_desc 10)])) == 1#1) : Bool))) ) : SailME
                    (FaultRecord × AddressDescriptor) Bool )
                  if (w__26 : Bool)
                  then
                    (do
                      let tlbrecord ← (( do (undefined_TLBRecord (← occLabel 1588) ()) ) :
                        SailME (FaultRecord × AddressDescriptor) TLBRecord )
                      let tlbrecord ← (( do
                        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 10)])) == 1#1) : Bool)
                        then
                          (do
                            let tlbentry ← (( do (S2TLBLookup descpaddr.tlbcontext) ) : SailME
                              (FaultRecord × AddressDescriptor) TLBLine )
                            ArmFull.assert tlbentry.valid_name "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:27304.38-27304.39"
                            let tlbrecord : TLBRecord := tlbentry.tlbrecord
                            (pure (tlbrecord)))
                        else
                          (do
                            let tlbrecord : TLBRecord :=
                              { tlbrecord with context := descpaddr.tlbcontext }
                            let tlbrecord : TLBRecord :=
                              { tlbrecord with context := { tlbrecord.context with xs := walkstate.memattrs.xs } }
                            let tlbrecord : TLBRecord :=
                              { tlbrecord with context := { tlbrecord.context with level := walkstate.level } }
                            let tlbrecord : TLBRecord :=
                              { tlbrecord with context := { tlbrecord.context with includes_s2_name := true } }
                            let tlbrecord : TLBRecord :=
                              { tlbrecord with context := { tlbrecord.context with isd128 := (walkparams.d128 == 1#1) } }
                            let tlbrecord : TLBRecord := { tlbrecord with walkstate := walkstate }
                            let tlbrecord : TLBRecord :=
                              { tlbrecord with blocksize := (TranslationSize walkparams.d128
                                  walkparams.tgx walkstate.level) }
                            if ((walkstate.contiguous == 1#1) : Bool)
                            then
                              (do
                                let w__27 ← (( do
                                  (ContiguousSize walkparams.d128 walkparams.tgx walkstate.level) )
                                  : SailME (FaultRecord × AddressDescriptor) Int )
                                let tlbrecord :=
                                  ({ tlbrecord with contigsize := w__27 } : TLBRecord)
                                (pure (tlbrecord)))
                            else
                              (let tlbrecord : TLBRecord := { tlbrecord with contigsize := 0 }
                              (pure (tlbrecord)))) ) : SailME (FaultRecord × AddressDescriptor)
                        TLBRecord )
                      let tlbrecord : TLBRecord :=
                        if ((walkparams.d128 == 1#1) : Bool)
                        then { tlbrecord with s2descriptor := mem_desc }
                        else
                          (let tlbrecord : TLBRecord :=
                            { tlbrecord with s2descriptor := (Sail.BitVec.updateSubrange
                                tlbrecord.s2descriptor 63 0 (Sail.BitVec.extractLsb mem_desc 63 0)) }
                          { tlbrecord with s2descriptor := (Sail.BitVec.updateSubrange
                              tlbrecord.s2descriptor 127 64 (Zeros (n := 64))) })
                      (pure ((S2TLBCache tlbrecord))))
                  else (pure (()))
                  if ((bne fault.statuscode Fault_None) : Bool)
                  then
                    (do
                      let w__28 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
                        (FaultRecord × AddressDescriptor) AddressDescriptor )
                      (pure ((fault, w__28))))
                  else
                    (do
                      let ipa_64 : (BitVec 64) := (Sail.BitVec.zeroExtend ipa.paddress.address 64)
                      let oa ← (( do (StageOA ipa_64 walkparams.d128 walkparams.tgx walkstate) ) :
                        SailME (FaultRecord × AddressDescriptor) FullAddress )
                      let s2_memattrs ← (( do (undefined_MemoryAttributes (← occLabel 1589) ())
                        ) : SailME (FaultRecord × AddressDescriptor) MemoryAttributes )
                      let w__35 ← (( do
                        if ((← do
                             if (((((BEq.beq accdesc.acctype AccessType_TTW) && (BEq.beq
                                      walkstate.memattrs.memtype MemType_Device)) && (walkparams.ptw == 0#1)) : Bool) : Bool)
                             then (pure true)
                             else
                               (do
                                 if (((BEq.beq accdesc.acctype AccessType_IFETCH) : Bool) : Bool)
                                 then
                                   (do
                                     if (((BEq.beq walkstate.memattrs.memtype MemType_Device) : Bool) : Bool)
                                     then (pure true)
                                     else
                                       (do
                                         let w__29 ← (( do readReg HCR_EL2 ) : SailME
                                           (FaultRecord × AddressDescriptor) (BitVec 64) )
                                         (pure ((((_get_HCR_EL2_Type_ID w__29) == 1#1) : Bool)))))
                                 else (pure false))) : Bool)
                        then (pure true)
                        else
                          (do
                            if ((((bne accdesc.acctype AccessType_IFETCH) && (BEq.beq
                                   walkstate.memattrs.memtype MemType_Normal)) : Bool) : Bool)
                            then
                              (do
                                let w__33 ← (( do readReg HCR_EL2 ) : SailME
                                  (FaultRecord × AddressDescriptor) (BitVec 64) )
                                (pure ((((_get_HCR_EL2_Type_CD w__33) == 1#1) : Bool))))
                            else (pure false)) ) : SailME (FaultRecord × AddressDescriptor) Bool )
                      let s2_memattrs ← (( do
                        if (w__35 : Bool)
                        then
                          (do
                            let w__36 ← (( do (NormalNCMemAttr ()) ) : SailME
                              (FaultRecord × AddressDescriptor) MemoryAttributes )
                            let s2_memattrs := (w__36 : MemoryAttributes)
                            let s2_memattrs : MemoryAttributes :=
                              { s2_memattrs with xs := walkstate.memattrs.xs }
                            (pure (s2_memattrs)))
                        else
                          (let s2_memattrs : MemoryAttributes := walkstate.memattrs
                          (pure (s2_memattrs))) ) : SailME (FaultRecord × AddressDescriptor)
                        MemoryAttributes )
                      let fault ← (( do
                        if ((accdesc.ls64 && (BEq.beq s2_memattrs.memtype MemType_Normal)) : Bool)
                        then
                          (do
                            if (((s2_memattrs.inner.attrs != MemAttr_NC) || (s2_memattrs.outer.attrs != MemAttr_NC)) : Bool)
                            then
                              (do
                                let fault : FaultRecord :=
                                  { fault with statuscode := Fault_Exclusive }
                                let w__37 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
                                  (FaultRecord × AddressDescriptor) AddressDescriptor )
                                SailME.throw ((fault, w__37) : (FaultRecord × AddressDescriptor))
                                (pure (fault)))
                            else (pure (fault)))
                        else (pure (fault)) ) : SailME (FaultRecord × AddressDescriptor)
                        FaultRecord )
                      let s2aarch64 : Bool := true
                      let memattrs ← (( do (undefined_MemoryAttributes (← occLabel 1590) ()) ) :
                        SailME (FaultRecord × AddressDescriptor) MemoryAttributes )
                      let memattrs ← (( do
                        if ((walkparams.fwb == 0#1) : Bool)
                        then
                          (do
                            (S2CombineS1MemAttrs ipa.memattrs s2_memattrs s2aarch64))
                        else (pure (s2_memattrs)) ) : SailME (FaultRecord × AddressDescriptor)
                        MemoryAttributes )
                      let pa ← (( do (CreateAddressDescriptor ipa.vaddress oa memattrs) ) : SailME
                        (FaultRecord × AddressDescriptor) AddressDescriptor )
                      let pa : AddressDescriptor := { pa with tlbcontext := descpaddr.tlbcontext }
                      let pa : AddressDescriptor := { pa with s2fs1mro := s2fs1mro }
                      let w__39 ← (( do
                        (AArch64_S2OutputMECID walkparams pa.paddress.paspace descriptor) ) : SailME
                        (FaultRecord × AddressDescriptor) (BitVec 16) )
                      let pa := ({ pa with mecid := w__39 } : AddressDescriptor)
                      (pure ((fault, pa))))))))


end ArmFull.Functions
