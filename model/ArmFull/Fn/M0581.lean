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
import ArmFull.Fn.M0034
import ArmFull.Fn.M0042
import ArmFull.Fn.M0049
import ArmFull.Fn.M0051
import ArmFull.Fn.M0097
import ArmFull.Fn.M0117
import ArmFull.Fn.M0119
import ArmFull.Fn.M0120
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0152
import ArmFull.Fn.M0155
import ArmFull.Fn.M0156
import ArmFull.Fn.M0166
import ArmFull.Fn.M0171
import ArmFull.Fn.M0172
import ArmFull.Fn.M0173
import ArmFull.Fn.M0179
import ArmFull.Fn.M0181
import ArmFull.Fn.M0185
import ArmFull.Fn.M0195
import ArmFull.Fn.M0217
import ArmFull.Fn.M0227
import ArmFull.Fn.M0237
import ArmFull.Fn.M0238
import ArmFull.Fn.M0244
import ArmFull.Fn.M0247
import ArmFull.Fn.M0252
import ArmFull.Fn.M0255
import ArmFull.Fn.M0257

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

/-- Type quantifiers: k_is_combined : Bool -/
def AuthDA (x : (BitVec 64)) (y : (BitVec 64)) (is_combined : Bool) : SailM (BitVec 64) := do
  let TrapEL2 ← (( do (undefined_bool_at (← occLabel 1333) ()) ) : SailM Bool )
  let TrapEL3 ← (( do (undefined_bool_at (← occLabel 1334) ()) ) : SailM Bool )
  let Enable ← (( do (undefined_bitvector_at (← occLabel 1335) 1) ) : SailM (BitVec 1) )
  let w__0 ← (( do readReg APDAKeyHi_EL1 ) : SailM (BitVec 64) )
  let w__1 ← (( do readReg APDAKeyLo_EL1 ) : SailM (BitVec 64) )
  let APDAKey_EL1 : (BitVec 128) :=
    ((Sail.BitVec.extractLsb w__0 63 0) +++ (Sail.BitVec.extractLsb w__1 63 0))
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let questionMark := w__2.EL
  let (Enable, TrapEL2, TrapEL3) ← (( do
    if ((questionMark == EL0) : Bool)
    then
      (do
        let w__3 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
        let IsEL1Regime : Bool := (w__3 == EL1)
        let w__6 ← (( do
          if (IsEL1Regime : Bool)
          then
            (do
              let w__4 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_SCTLR_EL1_Type_EnDA w__4))))
          else
            (do
              let w__5 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_SCTLR_EL2_Type_EnDA w__5)))) ) : SailM (BitVec 1) )
        let Enable := (w__6 : (BitVec 1))
        let w__13 ← (( do
          if ((← do
               if ((← do
                    (EL2Enabled ())) : Bool)
               then
                 (do
                   let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCR_EL2_Type_API w__8) == 0#1) : Bool))))
               else (pure false)) : Bool)
          then
            (do
              if ((← do
                   let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCR_EL2_Type_TGE w__10) == 0#1) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__11 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_E2H w__11) == 0#1) : Bool)))))
          else (pure false) ) : SailM Bool )
        let TrapEL2 := (w__13 : Bool)
        let w__15 ← (( do
          if (((HaveEL EL3) : Bool) : Bool)
          then
            (do
              let w__14 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
              (pure ((((_get_SCR_EL3_Type_API w__14) == 0#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let TrapEL3 := (w__15 : Bool)
        (pure ((Enable, TrapEL2, TrapEL3))))
    else
      (do
        if ((questionMark == EL1) : Bool)
        then
          (do
            let w__16 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            let Enable := ((_get_SCTLR_EL1_Type_EnDA w__16) : (BitVec 1))
            let w__19 ← (( do
              if ((← do
                   (EL2Enabled ())) : Bool)
              then
                (do
                  let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_API w__18) == 0#1) : Bool))))
              else (pure false) ) : SailM Bool )
            let TrapEL2 := (w__19 : Bool)
            let w__21 ← (( do
              if (((HaveEL EL3) : Bool) : Bool)
              then
                (do
                  let w__20 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                  (pure ((((_get_SCR_EL3_Type_API w__20) == 0#1) : Bool))))
              else (pure false) ) : SailM Bool )
            let TrapEL3 := (w__21 : Bool)
            (pure ((Enable, TrapEL2, TrapEL3))))
        else
          (do
            if ((questionMark == EL2) : Bool)
            then
              (do
                let w__22 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
                let Enable := ((_get_SCTLR_EL2_Type_EnDA w__22) : (BitVec 1))
                let TrapEL2 : Bool := false
                let w__24 ← (( do
                  if (((HaveEL EL3) : Bool) : Bool)
                  then
                    (do
                      let w__23 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                      (pure ((((_get_SCR_EL3_Type_API w__23) == 0#1) : Bool))))
                  else (pure false) ) : SailM Bool )
                let TrapEL3 := (w__24 : Bool)
                (pure ((Enable, TrapEL2, TrapEL3))))
            else
              (do
                if ((questionMark == EL3) : Bool)
                then
                  (do
                    let w__25 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
                    let Enable := ((_get_SCTLR_EL3_Type_EnDA w__25) : (BitVec 1))
                    let TrapEL2 : Bool := false
                    let TrapEL3 : Bool := false
                    (pure ((Enable, TrapEL2, TrapEL3))))
                else (pure ((Enable, TrapEL2, TrapEL3)))))) ) : SailM ((BitVec 1) × Bool × Bool) )
  if ((Enable == 0#1) : Bool)
  then (pure (x))
  else
    (do
      let w__27 ← (( do
        if ((TrapEL3 : Bool) : Bool)
        then
          (do
            (EL3SDDUndefPriority ()))
        else (pure false) ) : SailM Bool )
      if (w__27 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if (TrapEL2 : Bool)
          then
            (do
              (TrapPACUse EL2)
              (undefined_bitvector_at (← occLabel 1337) 64))
          else
            (do
              if (TrapEL3 : Bool)
              then
                (do
                  let w__30 ← (( do (EL3SDDUndef ()) ) : SailM Bool )
                  if (w__30 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      (TrapPACUse EL3)
                      (undefined_bitvector_at (← occLabel 1336) 64)))
              else
                (do
                  (Auth x y APDAKey_EL1 true 0#1 is_combined)))))


/-- Type quantifiers: k_is_combined : Bool -/
def AuthDB (x : (BitVec 64)) (y : (BitVec 64)) (is_combined : Bool) : SailM (BitVec 64) := do
  let TrapEL2 ← (( do (undefined_bool_at (← occLabel 1338) ()) ) : SailM Bool )
  let TrapEL3 ← (( do (undefined_bool_at (← occLabel 1339) ()) ) : SailM Bool )
  let Enable ← (( do (undefined_bitvector_at (← occLabel 1340) 1) ) : SailM (BitVec 1) )
  let w__0 ← (( do readReg APDBKeyHi_EL1 ) : SailM (BitVec 64) )
  let w__1 ← (( do readReg APDBKeyLo_EL1 ) : SailM (BitVec 64) )
  let APDBKey_EL1 : (BitVec 128) :=
    ((Sail.BitVec.extractLsb w__0 63 0) +++ (Sail.BitVec.extractLsb w__1 63 0))
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let questionMark := w__2.EL
  let (Enable, TrapEL2, TrapEL3) ← (( do
    if ((questionMark == EL0) : Bool)
    then
      (do
        let w__3 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
        let IsEL1Regime : Bool := (w__3 == EL1)
        let w__6 ← (( do
          if (IsEL1Regime : Bool)
          then
            (do
              let w__4 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_SCTLR_EL1_Type_EnDB w__4))))
          else
            (do
              let w__5 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_SCTLR_EL2_Type_EnDB w__5)))) ) : SailM (BitVec 1) )
        let Enable := (w__6 : (BitVec 1))
        let w__13 ← (( do
          if ((← do
               if ((← do
                    (EL2Enabled ())) : Bool)
               then
                 (do
                   let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCR_EL2_Type_API w__8) == 0#1) : Bool))))
               else (pure false)) : Bool)
          then
            (do
              if ((← do
                   let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCR_EL2_Type_TGE w__10) == 0#1) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__11 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_E2H w__11) == 0#1) : Bool)))))
          else (pure false) ) : SailM Bool )
        let TrapEL2 := (w__13 : Bool)
        let w__15 ← (( do
          if (((HaveEL EL3) : Bool) : Bool)
          then
            (do
              let w__14 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
              (pure ((((_get_SCR_EL3_Type_API w__14) == 0#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let TrapEL3 := (w__15 : Bool)
        (pure ((Enable, TrapEL2, TrapEL3))))
    else
      (do
        if ((questionMark == EL1) : Bool)
        then
          (do
            let w__16 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            let Enable := ((_get_SCTLR_EL1_Type_EnDB w__16) : (BitVec 1))
            let w__19 ← (( do
              if ((← do
                   (EL2Enabled ())) : Bool)
              then
                (do
                  let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_API w__18) == 0#1) : Bool))))
              else (pure false) ) : SailM Bool )
            let TrapEL2 := (w__19 : Bool)
            let w__21 ← (( do
              if (((HaveEL EL3) : Bool) : Bool)
              then
                (do
                  let w__20 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                  (pure ((((_get_SCR_EL3_Type_API w__20) == 0#1) : Bool))))
              else (pure false) ) : SailM Bool )
            let TrapEL3 := (w__21 : Bool)
            (pure ((Enable, TrapEL2, TrapEL3))))
        else
          (do
            if ((questionMark == EL2) : Bool)
            then
              (do
                let w__22 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
                let Enable := ((_get_SCTLR_EL2_Type_EnDB w__22) : (BitVec 1))
                let TrapEL2 : Bool := false
                let w__24 ← (( do
                  if (((HaveEL EL3) : Bool) : Bool)
                  then
                    (do
                      let w__23 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                      (pure ((((_get_SCR_EL3_Type_API w__23) == 0#1) : Bool))))
                  else (pure false) ) : SailM Bool )
                let TrapEL3 := (w__24 : Bool)
                (pure ((Enable, TrapEL2, TrapEL3))))
            else
              (do
                if ((questionMark == EL3) : Bool)
                then
                  (do
                    let w__25 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
                    let Enable := ((_get_SCTLR_EL3_Type_EnDB w__25) : (BitVec 1))
                    let TrapEL2 : Bool := false
                    let TrapEL3 : Bool := false
                    (pure ((Enable, TrapEL2, TrapEL3))))
                else (pure ((Enable, TrapEL2, TrapEL3)))))) ) : SailM ((BitVec 1) × Bool × Bool) )
  if ((Enable == 0#1) : Bool)
  then (pure (x))
  else
    (do
      let w__27 ← (( do
        if ((TrapEL3 : Bool) : Bool)
        then
          (do
            (EL3SDDUndefPriority ()))
        else (pure false) ) : SailM Bool )
      if (w__27 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if (TrapEL2 : Bool)
          then
            (do
              (TrapPACUse EL2)
              (undefined_bitvector_at (← occLabel 1342) 64))
          else
            (do
              if (TrapEL3 : Bool)
              then
                (do
                  let w__30 ← (( do (EL3SDDUndef ()) ) : SailM Bool )
                  if (w__30 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      (TrapPACUse EL3)
                      (undefined_bitvector_at (← occLabel 1341) 64)))
              else
                (do
                  (Auth x y APDBKey_EL1 true 1#1 is_combined)))))


def AArch64_CheckSystemAccess (op0 : (BitVec 2)) (op1 : (BitVec 3)) (crn : (BitVec 4)) (crm : (BitVec 4)) (op2 : (BitVec 3)) (rt : (BitVec 5)) (read : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveBTIExt ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (BranchTargetCheck ()))
  else (pure (()))
  let w__5 ← (( do
    if ((← do
         if ((← do
              (HaveTME ())) : Bool)
         then
           (do
             let w__2 ← (( do readReg TSTATE ) : SailM TMState )
             (pure (((w__2.depth >b 0) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__4 ← (( do (CheckTransactionalSystemAccess op0 op1 crn crm op2 read) ) : SailM Bool
          )
        (pure (((! w__4) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      (FailTransaction TMFailure_ERR false))
  else (pure (()))


/-- Type quantifiers: k_aligned : Bool -/
def AArch64_S1Translate (fault_in : FaultRecord) (regime : Regime) (va : (BitVec 64)) (aligned : Bool) (accdesc : AccessDescriptor) : SailM (FaultRecord × AddressDescriptor) := SailME.run do
  let descaccess ← (( do (undefined_AccessDescriptor (← occLabel 1608) ()) ) : SailME
    (FaultRecord × AddressDescriptor) AccessDescriptor )
  let s1aarch64 ← (( do (undefined_bool_at (← occLabel 1609) ()) ) : SailME
    (FaultRecord × AddressDescriptor) Bool )
  let s2aligned ← (( do (undefined_bool_at (← occLabel 1610) ()) ) : SailME
    (FaultRecord × AddressDescriptor) Bool )
  let tlbentry ← (( do (undefined_TLBLine (← occLabel 1611) ()) ) : SailME
    (FaultRecord × AddressDescriptor) TLBLine )
  let fault : FaultRecord := fault_in
  let fault : FaultRecord := { fault with secondstage := false }
  let fault : FaultRecord := { fault with s2fs1walk := false }
  let w__0 ← (( do (AArch64_S1Enabled regime accdesc.acctype) ) : SailME
    (FaultRecord × AddressDescriptor) Bool )
  if ((! w__0) : Bool)
  then
    (do
      (AArch64_S1DisabledOutput fault regime va accdesc aligned))
  else
    (do
      let walkparams ← (( do (AArch64_GetS1TTWParams regime accdesc.ss va) ) : SailME
        (FaultRecord × AddressDescriptor) S1TTWParams )
      let s1mintxsz ← (( do
        (AArch64_S1MinTxSZ regime walkparams.d128 walkparams.ds walkparams.tgx) ) : SailME
        (FaultRecord × AddressDescriptor) Int )
      let s1maxtxsz ← (( do (AArch64_MaxTxSZ walkparams.tgx) ) : SailME
        (FaultRecord × AddressDescriptor) Int )
      let w__2 ← (( do (AArch64_S1TxSZFaults regime walkparams) ) : SailME
        (FaultRecord × AddressDescriptor) Bool )
      if (w__2 : Bool)
      then
        (do
          let fault : FaultRecord := { fault with statuscode := Fault_Translation }
          let fault : FaultRecord := { fault with level := 0 }
          let w__3 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
            (FaultRecord × AddressDescriptor) AddressDescriptor )
          (pure ((fault, w__3))))
      else
        (do
          let walkparams : S1TTWParams :=
            if (((BitVec.toNat walkparams.txsz) <b s1mintxsz) : Bool)
            then { walkparams with txsz := (integer_subrange s1mintxsz 5 0) }
            else
              (if (((BitVec.toNat walkparams.txsz) >b s1maxtxsz) : Bool)
              then { walkparams with txsz := (integer_subrange s1maxtxsz 5 0) }
              else walkparams)
          if ((AArch64_VAIsOutOfRange va accdesc.acctype regime walkparams) : Bool)
          then
            (do
              let fault : FaultRecord := { fault with statuscode := Fault_Translation }
              let fault : FaultRecord := { fault with level := 0 }
              let w__4 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
                (FaultRecord × AddressDescriptor) AddressDescriptor )
              (pure ((fault, w__4))))
          else
            (do
              if (((accdesc.el == EL0) && (walkparams.e0pd == 1#1)) : Bool)
              then
                (do
                  let fault : FaultRecord := { fault with statuscode := Fault_Translation }
                  let fault : FaultRecord := { fault with level := 0 }
                  let w__5 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
                    (FaultRecord × AddressDescriptor) AddressDescriptor )
                  (pure ((fault, w__5))))
              else
                (do
                  let w__9 ← (( do
                    (pure ((← do
                          (pure ((← do
                                (pure ((← do
                                      (HaveTME ())) && ((accdesc.el == EL0) : Bool)))) && ((walkparams.nfd == 1#1) : Bool)))) && (accdesc.transactional : Bool)))
                    ) : SailME (FaultRecord × AddressDescriptor) Bool )
                  if (w__9 : Bool)
                  then
                    (do
                      let fault : FaultRecord := { fault with statuscode := Fault_Translation }
                      let fault : FaultRecord := { fault with level := 0 }
                      let w__10 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
                        (FaultRecord × AddressDescriptor) AddressDescriptor )
                      (pure ((fault, w__10))))
                  else
                    (do
                      let w__14 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    (pure ((← do
                                          (HaveSVE ())) && ((accdesc.el == EL0) : Bool)))) && ((walkparams.nfd == 1#1) : Bool)))) && (((accdesc.nonfault && accdesc.contiguous) || ((accdesc.firstfault && (! accdesc.first)) && (! accdesc.contiguous))) : Bool)))
                        ) : SailME (FaultRecord × AddressDescriptor) Bool )
                      if (w__14 : Bool)
                      then
                        (do
                          let fault : FaultRecord := { fault with statuscode := Fault_Translation }
                          let fault : FaultRecord := { fault with level := 0 }
                          let w__15 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
                            (FaultRecord × AddressDescriptor) AddressDescriptor )
                          (pure ((fault, w__15))))
                      else
                        (do
                          let descipaddr ← (( do
                            (undefined_AddressDescriptor (← occLabel 1612) ()) ) : SailME
                            (FaultRecord × AddressDescriptor) AddressDescriptor )
                          let walkstate ← (( do (undefined_TTWState (← occLabel 1613) ()) ) :
                            SailME (FaultRecord × AddressDescriptor) TTWState )
                          let descriptor ← (( do (undefined_bitvector_at (← occLabel 1614) 128)
                            ) : SailME (FaultRecord × AddressDescriptor) (BitVec 128) )
                          let new_desc ← (( do (undefined_bitvector_at (← occLabel 1615) 128) )
                            : SailME (FaultRecord × AddressDescriptor) (BitVec 128) )
                          let mem_desc ← (( do (undefined_bitvector_at (← occLabel 1616) 128) )
                            : SailME (FaultRecord × AddressDescriptor) (BitVec 128) )
                          let (descaccess, descipaddr, descriptor, fault, mem_desc, new_desc, s1aarch64, s2aligned, walkstate) ← (( do
                            let loop_vars ← sailUntilFuelM (fuel := 1048576) (fun (descaccess, descipaddr, descriptor, fault, mem_desc, new_desc, s1aarch64, s2aligned, walkstate) => (pure ((new_desc == descriptor) || (mem_desc == new_desc)))) (descaccess, descipaddr, descriptor, fault, mem_desc, new_desc, s1aarch64, s2aligned, walkstate)
                              fun (descaccess, descipaddr, descriptor, fault, mem_desc, new_desc, s1aarch64, s2aligned, walkstate) => do
                                let (descipaddr, descriptor, fault, walkstate) ← (( do
                                  if ((walkparams.d128 == 1#1) : Bool)
                                  then
                                    (do
                                      let w__16 ← (( do
                                        (AArch64_S1Walk fault walkparams va regime accdesc 128) ) :
                                        SailME (FaultRecord × AddressDescriptor)
                                        (FaultRecord × AddressDescriptor × TTWState × (BitVec 128))
                                        )
                                      let (tup__0, tup__1, tup__2, tup__3) :=
                                        (w__16 : (FaultRecord × AddressDescriptor × TTWState × (BitVec 128)))
                                      let fault : FaultRecord := tup__0
                                      let descipaddr : AddressDescriptor := tup__1
                                      let walkstate : TTWState := tup__2
                                      let descriptor : (BitVec 128) := tup__3
                                      (pure ((descipaddr, descriptor, fault, walkstate))))
                                  else
                                    (do
                                      let w__17 ← (( do
                                        (AArch64_S1Walk fault walkparams va regime accdesc 64) ) :
                                        SailME (FaultRecord × AddressDescriptor)
                                        (FaultRecord × AddressDescriptor × TTWState × (BitVec 64))
                                        )
                                      let (tup__0, tup__1, tup__2, tup__3) :=
                                        (w__17 : (FaultRecord × AddressDescriptor × TTWState × (BitVec 64)))
                                      let fault : FaultRecord := tup__0
                                      let descipaddr : AddressDescriptor := tup__1
                                      let walkstate : TTWState := tup__2
                                      let descriptor : (BitVec 128) :=
                                        (Sail.BitVec.updateSubrange descriptor 63 0 tup__3)
                                      let descriptor : (BitVec 128) :=
                                        (Sail.BitVec.updateSubrange descriptor 127 64
                                          (Zeros (n := 64)))
                                      (pure ((descipaddr, descriptor, fault, walkstate)))) ) :
                                  SailME (FaultRecord × AddressDescriptor)
                                  (AddressDescriptor × (BitVec 128) × FaultRecord × TTWState) )
                                let (descaccess, fault, mem_desc, new_desc, s1aarch64, s2aligned) ← (( do
                                  if ((bne fault.statuscode Fault_None) : Bool)
                                  then
                                    (do
                                      let w__18 ← (( do (__UNKNOWN_AddressDescriptor ()) ) :
                                        SailME (FaultRecord × AddressDescriptor) AddressDescriptor
                                        )
                                      SailME.throw ((fault, w__18) : (FaultRecord × AddressDescriptor))
                                      (pure ((descaccess, fault, mem_desc, new_desc, s1aarch64, s2aligned))))
                                  else
                                    (do
                                      if ((BEq.beq accdesc.acctype AccessType_IFETCH) : Bool)
                                      then
                                        (do
                                          (SetInGuardedPage (walkstate.guardedpage == 1#1)))
                                      else (pure (()))
                                      let w__19 ← (( do
                                        (AArch64_S1HasAlignmentFault accdesc aligned
                                          walkparams.ntlsmd walkstate.memattrs) ) : SailME
                                        (FaultRecord × AddressDescriptor) Bool )
                                      let fault : FaultRecord :=
                                        if (w__19 : Bool)
                                        then { fault with statuscode := Fault_Alignment }
                                        else fault
                                      let fault ← (( do
                                        if ((BEq.beq fault.statuscode Fault_None) : Bool)
                                        then
                                          (do
                                            (AArch64_S1CheckPermissions fault regime walkstate
                                              walkparams accdesc))
                                        else (pure (fault)) ) : SailME
                                        (FaultRecord × AddressDescriptor) FaultRecord )
                                      let new_desc : (BitVec 128) := descriptor
                                      let w__22 ← (( do
                                        if (((walkparams.ha == 1#1) : Bool) : Bool)
                                        then
                                          (do
                                            (AArch64_SettingAccessFlagPermitted fault))
                                        else (pure false) ) : SailME
                                        (FaultRecord × AddressDescriptor) Bool )
                                      let new_desc : (BitVec 128) :=
                                        if (w__22 : Bool)
                                        then (BitVec.update new_desc 10 (Bit 1#1))
                                        else new_desc
                                      let w__28 ← (( do
                                        (pure ((← do
                                              (pure ((← do
                                                    (pure ((← do
                                                          (pure ((← do
                                                                (pure ((← do
                                                                      (AArch64_SettingDirtyStatePermitted
                                                                        fault)) && ((walkparams.ha == 1#1) : Bool)))) && ((walkparams.hd == 1#1) : Bool)))) && (((walkparams.pie == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                descriptor 51)])) == 1#1)) : Bool)))) && (accdesc.write : Bool)))) && ((! ((BEq.beq
                                                  accdesc.acctype AccessType_AT) || ((BEq.beq
                                                    accdesc.acctype AccessType_IC) || (BEq.beq
                                                    accdesc.acctype AccessType_DC)))) : Bool))) ) :
                                        SailME (FaultRecord × AddressDescriptor) Bool )
                                      let new_desc : (BitVec 128) :=
                                        if (w__28 : Bool)
                                        then (BitVec.update new_desc 7 (Bit 0#1))
                                        else new_desc
                                      let (descaccess, fault, mem_desc, s1aarch64, s2aligned) ← (( do
                                        if ((new_desc != descriptor) : Bool)
                                        then
                                          (do
                                            let descpaddr ← (( do
                                              (undefined_AddressDescriptor (← occLabel 1619) ()) )
                                              : SailME (FaultRecord × AddressDescriptor)
                                              AddressDescriptor )
                                            let w__29 ← (( do (CreateAccDescTTEUpdate accdesc) ) :
                                              SailME (FaultRecord × AddressDescriptor)
                                              AccessDescriptor )
                                            let descaccess := (w__29 : AccessDescriptor)
                                            let w__31 ← (( do
                                              if (((BEq.beq regime Regime_EL10) : Bool) : Bool)
                                              then
                                                (do
                                                  (EL2Enabled ()))
                                              else (pure false) ) : SailME
                                              (FaultRecord × AddressDescriptor) Bool )
                                            let (descpaddr, s1aarch64, s2aligned) ← (( do
                                              if (w__31 : Bool)
                                              then
                                                (do
                                                  let s2fault ← (( do
                                                    (undefined_FaultRecord (← occLabel 1620) ()) )
                                                    : SailME (FaultRecord × AddressDescriptor)
                                                    FaultRecord )
                                                  let s1aarch64 : Bool := true
                                                  let s2aligned : Bool := true
                                                  let w__32 ← (( do
                                                    (AArch64_S2Translate fault descipaddr s1aarch64
                                                      none s2aligned descaccess) ) : SailME
                                                    (FaultRecord × AddressDescriptor)
                                                    (FaultRecord × AddressDescriptor) )
                                                  let (tup__0, tup__1) :=
                                                    (w__32 : (FaultRecord × AddressDescriptor))
                                                  let s2fault : FaultRecord := tup__0
                                                  let descpaddr : AddressDescriptor := tup__1
                                                  if ((bne s2fault.statuscode Fault_None) : Bool)
                                                  then
                                                    (do
                                                      let w__33 ← (( do
                                                        (__UNKNOWN_AddressDescriptor ()) ) : SailME
                                                        (FaultRecord × AddressDescriptor)
                                                        AddressDescriptor )
                                                      SailME.throw ((s2fault, w__33) : (FaultRecord × AddressDescriptor)))
                                                  else (pure (()))
                                                  (pure ((descpaddr, s1aarch64, s2aligned))))
                                              else
                                                (let descpaddr : AddressDescriptor := descipaddr
                                                (pure ((descpaddr, s1aarch64, s2aligned)))) ) :
                                              SailME (FaultRecord × AddressDescriptor)
                                              (AddressDescriptor × Bool × Bool) )
                                            let translation_info : TranslationInfo :=
                                              { regime := regime
                                                vmid := none
                                                asid := none
                                                va := va
                                                s1level := (some walkstate.level)
                                                s2info := none
                                                s1params := (some walkparams)
                                                s2params := none
                                                memattrs := walkstate.memattrs }
                                            let (fault, mem_desc) ← (( do
                                              if ((walkparams.d128 == 1#1) : Bool)
                                              then
                                                (do
                                                  let w__34 ← (( do
                                                    (AArch64_MemSwapTableDesc fault descriptor
                                                      new_desc walkparams.ee descaccess descpaddr
                                                      translation_info) ) : SailME
                                                    (FaultRecord × AddressDescriptor)
                                                    (FaultRecord × (BitVec 128)) )
                                                  let (tup__0, tup__1) :=
                                                    (w__34 : (FaultRecord × (BitVec 128)))
                                                  let fault : FaultRecord := tup__0
                                                  let mem_desc : (BitVec 128) := tup__1
                                                  (pure ((fault, mem_desc))))
                                              else
                                                (do
                                                  let w__35 ← (( do
                                                    (AArch64_MemSwapTableDesc fault
                                                      (Sail.BitVec.extractLsb descriptor 63 0)
                                                      (Sail.BitVec.extractLsb new_desc 63 0)
                                                      walkparams.ee descaccess descpaddr
                                                      translation_info) ) : SailME
                                                    (FaultRecord × AddressDescriptor)
                                                    (FaultRecord × (BitVec 64)) )
                                                  let (tup__0, tup__1) :=
                                                    (w__35 : (FaultRecord × (BitVec 64)))
                                                  let fault : FaultRecord := tup__0
                                                  let mem_desc : (BitVec 128) :=
                                                    (Sail.BitVec.updateSubrange mem_desc 63 0 tup__1)
                                                  let mem_desc : (BitVec 128) :=
                                                    (Sail.BitVec.updateSubrange mem_desc 127 64
                                                      (Zeros (n := 64)))
                                                  (pure ((fault, mem_desc)))) ) : SailME
                                              (FaultRecord × AddressDescriptor)
                                              (FaultRecord × (BitVec 128)) )
                                            (pure ((descaccess, fault, mem_desc, s1aarch64, s2aligned))))
                                        else
                                          (pure ((descaccess, fault, mem_desc, s1aarch64, s2aligned)))
                                        ) : SailME (FaultRecord × AddressDescriptor)
                                        (AccessDescriptor × FaultRecord × (BitVec 128) × Bool × Bool)
                                        )
                                      (pure ((descaccess, fault, mem_desc, new_desc, s1aarch64, s2aligned))))
                                  ) : SailME (FaultRecord × AddressDescriptor)
                                  (AccessDescriptor × FaultRecord × (BitVec 128) × (BitVec 128) × Bool × Bool)
                                  )
                                (pure ((descaccess, descipaddr, descriptor, fault, mem_desc, new_desc, s1aarch64, s2aligned, walkstate)))
                            (pure loop_vars) ) : SailME (FaultRecord × AddressDescriptor)
                            (AccessDescriptor × AddressDescriptor × (BitVec 128) × FaultRecord × (BitVec 128) × (BitVec 128) × Bool × Bool × TTWState)
                            )
                          let w__38 ← (( do
                            (pure ((← do
                                  (pure ((← do
                                        readReg __tlb_enabled) && ((new_desc != descriptor) : Bool)))) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                      mem_desc 10)])) == 1#1) : Bool))) ) : SailME
                            (FaultRecord × AddressDescriptor) Bool )
                          if (w__38 : Bool)
                          then
                            (do
                              let tlbrecord ← (( do (undefined_TLBRecord (← occLabel 1621) ()) )
                                : SailME (FaultRecord × AddressDescriptor) TLBRecord )
                              let tlbrecord ← (( do
                                if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 10)])) == 1#1) : Bool)
                                then
                                  (do
                                    let tlbentry ← (( do (S1TLBLookup descipaddr.tlbcontext) ) :
                                      SailME (FaultRecord × AddressDescriptor) TLBLine )
                                    ArmFull.assert tlbentry.valid_name "sail-arm/v8_base.sail:27700.38-27700.39"
                                    let tlbrecord : TLBRecord := tlbentry.tlbrecord
                                    (pure (tlbrecord)))
                                else
                                  (do
                                    let tlbrecord : TLBRecord :=
                                      { tlbrecord with context := descipaddr.tlbcontext }
                                    let tlbrecord : TLBRecord :=
                                      { tlbrecord with context := { tlbrecord.context with xs := walkstate.memattrs.xs } }
                                    let tlbrecord : TLBRecord :=
                                      { tlbrecord with context := { tlbrecord.context with level := walkstate.level } }
                                    let tlbrecord : TLBRecord :=
                                      { tlbrecord with context := { tlbrecord.context with nG := walkstate.nG } }
                                    let tlbrecord : TLBRecord :=
                                      { tlbrecord with context := { tlbrecord.context with isd128 := (walkparams.d128 == 1#1) } }
                                    let tlbrecord : TLBRecord :=
                                      { tlbrecord with walkstate := walkstate }
                                    let tlbrecord : TLBRecord :=
                                      { tlbrecord with blocksize := (TranslationSize walkparams.d128
                                          walkparams.tgx walkstate.level) }
                                    if ((walkstate.contiguous == 1#1) : Bool)
                                    then
                                      (do
                                        let w__39 ← (( do
                                          (ContiguousSize walkparams.d128 walkparams.tgx
                                            walkstate.level) ) : SailME
                                          (FaultRecord × AddressDescriptor) Int )
                                        let tlbrecord :=
                                          ({ tlbrecord with contigsize := w__39 } : TLBRecord)
                                        (pure (tlbrecord)))
                                    else
                                      (let tlbrecord : TLBRecord :=
                                        { tlbrecord with contigsize := 0 }
                                      (pure (tlbrecord)))) ) : SailME
                                (FaultRecord × AddressDescriptor) TLBRecord )
                              let tlbrecord : TLBRecord :=
                                if ((walkparams.d128 == 1#1) : Bool)
                                then { tlbrecord with s1descriptor := mem_desc }
                                else
                                  (let tlbrecord : TLBRecord :=
                                    { tlbrecord with s1descriptor := (Sail.BitVec.updateSubrange
                                        tlbrecord.s1descriptor 63 0
                                        (Sail.BitVec.extractLsb mem_desc 63 0)) }
                                  { tlbrecord with s1descriptor := (Sail.BitVec.updateSubrange
                                      tlbrecord.s1descriptor 127 64 (Zeros (n := 64))) })
                              (pure ((S1TLBCache tlbrecord))))
                          else (pure (()))
                          if ((bne fault.statuscode Fault_None) : Bool)
                          then
                            (do
                              let w__40 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
                                (FaultRecord × AddressDescriptor) AddressDescriptor )
                              (pure ((fault, w__40))))
                          else
                            (do
                              let oa ← (( do (StageOA va walkparams.d128 walkparams.tgx walkstate)
                                ) : SailME (FaultRecord × AddressDescriptor) FullAddress )
                              let memattrs ← (( do
                                (undefined_MemoryAttributes (← occLabel 1622) ()) ) : SailME
                                (FaultRecord × AddressDescriptor) MemoryAttributes )
                              let w__43 ← (( do
                                if (((BEq.beq accdesc.acctype AccessType_IFETCH) : Bool) : Bool)
                                then
                                  (do
                                    if (((BEq.beq walkstate.memattrs.memtype MemType_Device) : Bool) : Bool)
                                    then (pure true)
                                    else
                                      (do
                                        let w__41 ← (( do (AArch64_S1ICacheEnabled regime) ) :
                                          SailME (FaultRecord × AddressDescriptor) Bool )
                                        (pure (((! w__41) : Bool)))))
                                else (pure false) ) : SailME (FaultRecord × AddressDescriptor) Bool
                                )
                              let memattrs ← (( do
                                if (w__43 : Bool)
                                then
                                  (do
                                    let w__44 ← (( do (NormalNCMemAttr ()) ) : SailME
                                      (FaultRecord × AddressDescriptor) MemoryAttributes )
                                    let memattrs := (w__44 : MemoryAttributes)
                                    let memattrs : MemoryAttributes :=
                                      { memattrs with xs := walkstate.memattrs.xs }
                                    (pure (memattrs)))
                                else
                                  (do
                                    let w__47 ← (( do
                                      (pure ((← do
                                            if (((bne accdesc.acctype AccessType_IFETCH) : Bool) : Bool)
                                            then
                                              (do
                                                let w__45 ← (( do (AArch64_S1DCacheEnabled regime)
                                                  ) : SailME (FaultRecord × AddressDescriptor) Bool
                                                  )
                                                (pure (((! w__45) : Bool))))
                                            else (pure false)) && ((BEq.beq
                                            walkstate.memattrs.memtype MemType_Normal) : Bool))) ) :
                                      SailME (FaultRecord × AddressDescriptor) Bool )
                                    if (w__47 : Bool)
                                    then
                                      (do
                                        let w__48 ← (( do (NormalNCMemAttr ()) ) : SailME
                                          (FaultRecord × AddressDescriptor) MemoryAttributes )
                                        let memattrs := (w__48 : MemoryAttributes)
                                        let memattrs : MemoryAttributes :=
                                          { memattrs with xs := walkstate.memattrs.xs }
                                        let w__52 ← (( do
                                          if ((← do
                                               (pure ((← do
                                                     (HaveMTE2Ext ())) && ((BEq.beq
                                                     walkstate.memattrs.tags MemTag_AllocationTagged) : Bool)))) : Bool)
                                          then
                                            (do
                                              let w__51 ← (( do
                                                (ConstrainUnpredictableBool Unpredictable_S1CTAGGED)
                                                ) : SailME (FaultRecord × AddressDescriptor) Bool )
                                              (pure (((! w__51) : Bool))))
                                          else (pure false) ) : SailME
                                          (FaultRecord × AddressDescriptor) Bool )
                                        let memattrs : MemoryAttributes :=
                                          if (w__52 : Bool)
                                          then { memattrs with tags := MemTag_Untagged }
                                          else memattrs
                                        (pure (memattrs)))
                                    else
                                      (let memattrs : MemoryAttributes := walkstate.memattrs
                                      (pure (memattrs)))) ) : SailME
                                (FaultRecord × AddressDescriptor) MemoryAttributes )
                              let w__58 ← (( do
                                if ((← do
                                     if ((← do
                                          if (((BEq.beq regime Regime_EL10) : Bool) : Bool)
                                          then
                                            (do
                                              (EL2Enabled ()))
                                          else (pure false)) : Bool)
                                     then
                                       (do
                                         let w__55 ← (( do readReg HCR_EL2 ) : SailME
                                           (FaultRecord × AddressDescriptor) (BitVec 64) )
                                         (pure ((((_get_HCR_EL2_Type_VM w__55) == 1#1) : Bool))))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__57 ← (( do
                                      (__IMPDEF_boolean "Apply effective shareability at stage 1") )
                                      : SailME (FaultRecord × AddressDescriptor) Bool )
                                    (pure (((! w__57) : Bool))))
                                else (pure false) ) : SailME (FaultRecord × AddressDescriptor) Bool
                                )
                              let memattrs : MemoryAttributes :=
                                if (w__58 : Bool)
                                then
                                  { memattrs with shareability := walkstate.memattrs.shareability }
                                else
                                  { memattrs with shareability := (EffectiveShareability memattrs) }
                              let fault ← (( do
                                if ((accdesc.ls64 && (BEq.beq memattrs.memtype MemType_Normal)) : Bool)
                                then
                                  (do
                                    if (((memattrs.inner.attrs != MemAttr_NC) || (memattrs.outer.attrs != MemAttr_NC)) : Bool)
                                    then
                                      (do
                                        let fault : FaultRecord :=
                                          { fault with statuscode := Fault_Exclusive }
                                        let w__59 ← (( do (__UNKNOWN_AddressDescriptor ()) ) :
                                          SailME (FaultRecord × AddressDescriptor)
                                          AddressDescriptor )
                                        SailME.throw ((fault, w__59) : (FaultRecord × AddressDescriptor))
                                        (pure (fault)))
                                    else (pure (fault)))
                                else (pure (fault)) ) : SailME (FaultRecord × AddressDescriptor)
                                FaultRecord )
                              let ipa ← (( do (CreateAddressDescriptor va oa memattrs) ) : SailME
                                (FaultRecord × AddressDescriptor) AddressDescriptor )
                              let ipa : AddressDescriptor :=
                                { ipa with tlbcontext := descipaddr.tlbcontext }
                              let ipa : AddressDescriptor :=
                                { ipa with s1assured := walkstate.s1assured }
                              let varange : VARange := (AArch64_GetVARange va)
                              let w__60 ← (( do
                                (AArch64_S1OutputMECID walkparams regime varange
                                  ipa.paddress.paspace descriptor) ) : SailME
                                (FaultRecord × AddressDescriptor) (BitVec 16) )
                              let ipa := ({ ipa with mecid := w__60 } : AddressDescriptor)
                              (pure ((fault, ipa))))))))))


end ArmFull.Functions
