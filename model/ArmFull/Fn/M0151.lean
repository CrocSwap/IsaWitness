module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0008
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0019
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0144 set_option backward.proofsInPublic true @[expose] public section

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

def undefined_TLBRecord (ℓ : ChoiceLabel) (_ : Unit) : SailM TLBRecord := do
  let w__0 ← (( do (undefined_TLBContext (ℓ.child 0) ()) ) : SailM TLBContext )
  let w__1 ← (( do (undefined_TTWState (ℓ.child 1) ()) ) : SailM TTWState )
  let w__2 ← (( do (undefined_int_at (ℓ.child 2) ()) ) : SailM Int )
  let w__3 ← (( do (undefined_int_at (ℓ.child 3) ()) ) : SailM Int )
  let w__4 ← (( do (undefined_bitvector_at (ℓ.child 4) 128) ) : SailM (BitVec 128) )
  let w__5 ← (( do (undefined_bitvector_at (ℓ.child 5) 128) ) : SailM (BitVec 128) )
  (pure ({ context := w__0
           walkstate := w__1
           blocksize := w__2
           contigsize := w__3
           s1descriptor := w__4
           s2descriptor := w__5 }))


def undefined_TranslationStartInfo (ℓ : ChoiceLabel) (_ : Unit) : SailM TranslationStartInfo := do
  let w__0 ← (( do (undefined_SecurityState (ℓ.child 0) ()) ) : SailM SecurityState )
  let w__1 ← (( do (undefined_Regime (ℓ.child 1) ()) ) : SailM Regime )
  let w__2 ← (( do (undefined_bitvector_at (ℓ.child 2) 16) ) : SailM (BitVec 16) )
  let w__3 ← (( do (undefined_bitvector_at (ℓ.child 3) 16) ) : SailM (BitVec 16) )
  let w__4 ← (( do (undefined_bitvector_at (ℓ.child 4) 64) ) : SailM (BitVec 64) )
  let w__5 ← (( do (undefined_bitvector_at (ℓ.child 5) 1) ) : SailM (BitVec 1) )
  let w__6 ← (( do (undefined_AccessDescriptor (ℓ.child 6) ()) ) : SailM AccessDescriptor )
  let w__7 ← (( do (undefined_int_at (ℓ.child 7) ()) ) : SailM Int )
  (pure ({ ss := w__0
           regime := w__1
           vmid := w__2
           asid := w__3
           va := w__4
           cnp := w__5
           accdesc := w__6
           size := w__7 }))


/-- Type quantifiers: k_secure : Bool -/
def ELStateUsingAArch32K (el : (BitVec 2)) (secure : Bool) : SailM (Bool × Bool) := do
  let w__0 ← (( do (HaveAArch32EL el) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure ((true, false)))
  else
    (do
      if ((secure && (el == EL2)) : Bool)
      then (pure ((true, false)))
      else
        (do
          let w__1 ← (( do (HaveAArch64 ()) ) : SailM Bool )
          if ((! w__1) : Bool)
          then (pure ((true, true)))
          else
            (do
              let aarch32 ← (( do (__UNKNOWN_boolean ()) ) : SailM Bool )
              let known : Bool := true
              let aarch32_below_el3 ← (( do
                if ((← do
                     if ((← do
                          (HaveEL EL3)) : Bool)
                     then
                       (do
                         if ((← do
                              if (((! secure) : Bool) : Bool)
                              then (pure true)
                              else
                                (do
                                  let w__3 ← (( do (HaveSecureEL2Ext ()) ) : SailM Bool )
                                  (pure (((! w__3) : Bool))))) : Bool)
                         then (pure true)
                         else
                           (do
                             let w__5 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                             (pure ((((_get_SCR_EL3_Type_EEL2 w__5) == 0#1) : Bool)))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__8 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    (pure ((((_get_SCR_EL3_Type_RW w__8) == 0#1) : Bool))))
                else (pure false) ) : SailM Bool )
              let aarch32_at_el1 ← (( do
                if (aarch32_below_el3 : Bool)
                then (pure true)
                else
                  (do
                    if ((← do
                         if ((← do
                              if ((← do
                                   (HaveEL EL2)) : Bool)
                              then
                                (do
                                  if (((! secure) : Bool) : Bool)
                                  then (pure true)
                                  else
                                    (do
                                      if ((← do
                                           (HaveSecureEL2Ext ())) : Bool)
                                      then
                                        (do
                                          let w__11 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64)
                                            )
                                          (pure ((((_get_SCR_EL3_Type_EEL2 w__11) == 1#1) : Bool))))
                                      else (pure false)))
                              else (pure false)) : Bool)
                         then
                           (do
                             let w__18 ← (( do
                               if ((← do
                                    (HaveVirtHostExt ())) : Bool)
                               then
                                 (do
                                   let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                   let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                   (pure (((((_get_HCR_EL2_Type_E2H w__16) +++ (_get_HCR_EL2_Type_TGE
                                           w__17)) == 0b11#2) : Bool))))
                               else (pure false) ) : SailM Bool )
                             (pure (((! w__18) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__20 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure ((((_get_HCR_EL2_Type_RW w__20) == 0#1) : Bool))))
                    else (pure false)) ) : SailM Bool )
              let (aarch32, known) ← (( do
                if (((el == EL0) && (! aarch32_at_el1)) : Bool)
                then
                  (do
                    let w__22 ← (( do readReg PSTATE ) : SailM ProcState )
                    if ((w__22.EL == EL0) : Bool)
                    then
                      (do
                        let w__23 ← (( do readReg PSTATE ) : SailM ProcState )
                        let aarch32 := ((w__23.nRW == 1#1) : Bool)
                        (pure ((aarch32, known))))
                    else
                      (let known : Bool := false
                      (pure ((aarch32, known)))))
                else
                  (let aarch32 : Bool :=
                    ((aarch32_below_el3 && (el != EL3)) || (aarch32_at_el1 && ((el == EL1) || (el == EL0))))
                  (pure ((aarch32, known)))) ) : SailM (Bool × Bool) )
              let aarch32 ← (( do
                if ((! known) : Bool)
                then
                  (do
                    (__UNKNOWN_boolean ()))
                else (pure (aarch32)) ) : SailM Bool )
              (pure ((known, aarch32))))))


def SCR_GEN_read (_ : Unit) : SailM (BitVec 64) := do
  let w__0 ← (( do (HaveEL EL3) ) : SailM Bool )
  ArmFull.assert w__0 "sail-inputs/03-v8_base.sail:3479.22-3479.23"
  let r ← (( do (undefined_bitvector_at (← occLabel 490) 64) ) : SailM (BitVec 64) )
  let w__1 ← (( do (HaveAArch64 ()) ) : SailM Bool )
  let r ← (( do
    if ((! w__1) : Bool)
    then
      (do
        let w__2 ← (( do readReg SCR ) : SailM (BitVec 32) )
        let r := ((Sail.BitVec.zeroExtend w__2 64) : (BitVec 64))
        (pure (r)))
    else
      (do
        readReg SCR_EL3) ) : SailM (BitVec 64) )
  (pure ((Mk_SCRType r)))


def HighestEL (_ : Unit) : SailM (BitVec 2) := do
  let w__0 ← (( do (HaveEL EL3) ) : SailM Bool )
  if (w__0 : Bool)
  then (pure (EL3))
  else
    (do
      let w__1 ← (( do (HaveEL EL2) ) : SailM Bool )
      let w__2 : (BitVec 2) :=
        if (w__1 : Bool)
        then EL2
        else EL1
      (pure (w__2)))


def UsingAArch32 (_ : Unit) : SailM Bool := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let aarch32 : Bool := (w__0.nRW == 1#1)
  let w__1 ← (( do (HaveAArch32 ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then
    (do
      ArmFull.assert (! aarch32) "sail-inputs/03-v8_base.sail:4029.32-4029.33")
  else (pure (()))
  let w__2 ← (( do (HaveAArch64 ()) ) : SailM Bool )
  if ((! w__2) : Bool)
  then
    (do
      ArmFull.assert aarch32 "sail-inputs/03-v8_base.sail:4032.22-4032.23")
  else (pure (()))
  (pure (aarch32))


def ExternalNoninvasiveDebugEnabled (_ : Unit) : SailM Bool := do
  if ((← do
       if ((← do
            let w__0 ← (( do (HaveNoninvasiveDebugAuth ()) ) : SailM Bool )
            (pure (((! w__0) : Bool)))) : Bool)
       then (pure true)
       else
         (do
           (ExternalInvasiveDebugEnabled ()))) : Bool)
  then (pure true)
  else
    (do
      let w__3 ← (( do readReg NIDEN ) : SailM Signal )
      (pure (((BEq.beq w__3 Signal_High) : Bool))))


def SDER_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _SDER ) : SailM SDER_Type )
  let w__0 ← (( do (HaveEL EL3) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (SDER32_EL3_read ()) ) : SailM (BitVec 64) )
      let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__1 0 32)) : (BitVec 32))
      (pure (r)))
  else
    (do
      let w__2 ← (( do readReg SDER32_EL2 ) : SailM (BitVec 64) )
      let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__2 0 32)) : (BitVec 32))
      (pure (r)))


def SPEEvent (pmuevent : (BitVec 16)) : SailM Unit := SailME.run do
  let questionMark := pmuevent
  if ((questionMark == PMU_EVENT_DSNP_HIT_RD) : Bool)
  then
    (do
      let w__0 ← (( do (HaveStatisticalProfilingv1p4 ()) ) : SailME Unit Bool )
      if (w__0 : Bool)
      then
        (do
          let w__1 ← (( do readReg SPESampleEvents ) : SailME Unit (BitVec 64) )
          writeReg SPESampleEvents (BitVec.update w__1 23 (Bit 1#1)))
      else (pure (())))
  else
    (do
      if ((questionMark == PMU_EVENT_L1D_LFB_HIT_RD) : Bool)
      then
        (do
          let w__2 ← (( do (HaveStatisticalProfilingv1p4 ()) ) : SailME Unit Bool )
          if (w__2 : Bool)
          then
            (do
              let w__3 ← (( do readReg SPESampleEvents ) : SailME Unit (BitVec 64) )
              writeReg SPESampleEvents (BitVec.update w__3 22 (Bit 1#1)))
          else (pure (())))
      else
        (do
          if ((questionMark == PMU_EVENT_L2D_LFB_HIT_RD) : Bool)
          then
            (do
              let w__4 ← (( do (HaveStatisticalProfilingv1p4 ()) ) : SailME Unit Bool )
              if (w__4 : Bool)
              then
                (do
                  let w__5 ← (( do readReg SPESampleEvents ) : SailME Unit (BitVec 64) )
                  writeReg SPESampleEvents (BitVec.update w__5 22 (Bit 1#1)))
              else (pure (())))
          else
            (do
              if ((questionMark == PMU_EVENT_L3D_LFB_HIT_RD) : Bool)
              then
                (do
                  let w__6 ← (( do (HaveStatisticalProfilingv1p4 ()) ) : SailME Unit Bool )
                  if (w__6 : Bool)
                  then
                    (do
                      let w__7 ← (( do readReg SPESampleEvents ) : SailME Unit (BitVec 64) )
                      writeReg SPESampleEvents (BitVec.update w__7 22 (Bit 1#1)))
                  else (pure (())))
              else
                (do
                  if ((questionMark == PMU_EVENT_LL_LFB_HIT_RD) : Bool)
                  then
                    (do
                      let w__8 ← (( do (HaveStatisticalProfilingv1p4 ()) ) : SailME Unit Bool )
                      if (w__8 : Bool)
                      then
                        (do
                          let w__9 ← (( do readReg SPESampleEvents ) : SailME Unit (BitVec 64) )
                          writeReg SPESampleEvents (BitVec.update w__9 22 (Bit 1#1)))
                      else (pure (())))
                  else
                    (do
                      if ((questionMark == PMU_EVENT_L1D_CACHE_HITM_RD) : Bool)
                      then
                        (do
                          let w__10 ← (( do (HaveStatisticalProfilingv1p4 ()) ) : SailME Unit Bool
                            )
                          if (w__10 : Bool)
                          then
                            (do
                              let w__11 ← (( do readReg SPESampleEvents ) : SailME Unit
                                (BitVec 64) )
                              writeReg SPESampleEvents (BitVec.update w__11 21 (Bit 1#1)))
                          else (pure (())))
                      else
                        (do
                          if ((questionMark == PMU_EVENT_L2D_CACHE_HITM_RD) : Bool)
                          then
                            (do
                              let w__12 ← (( do (HaveStatisticalProfilingv1p4 ()) ) : SailME Unit
                                Bool )
                              if (w__12 : Bool)
                              then
                                (do
                                  let w__13 ← (( do readReg SPESampleEvents ) : SailME Unit
                                    (BitVec 64) )
                                  writeReg SPESampleEvents (BitVec.update w__13 21 (Bit 1#1)))
                              else (pure (())))
                          else
                            (do
                              if ((questionMark == PMU_EVENT_L3D_CACHE_HITM_RD) : Bool)
                              then
                                (do
                                  let w__14 ← (( do (HaveStatisticalProfilingv1p4 ()) ) : SailME
                                    Unit Bool )
                                  if (w__14 : Bool)
                                  then
                                    (do
                                      let w__15 ← (( do readReg SPESampleEvents ) : SailME Unit
                                        (BitVec 64) )
                                      writeReg SPESampleEvents (BitVec.update w__15 21 (Bit 1#1)))
                                  else (pure (())))
                              else
                                (do
                                  if ((questionMark == PMU_EVENT_LL_CACHE_HITM_RD) : Bool)
                                  then
                                    (do
                                      let w__16 ← (( do (HaveStatisticalProfilingv1p4 ()) ) :
                                        SailME Unit Bool )
                                      if (w__16 : Bool)
                                      then
                                        (do
                                          let w__17 ← (( do readReg SPESampleEvents ) : SailME
                                            Unit (BitVec 64) )
                                          writeReg SPESampleEvents (BitVec.update w__17 21 (Bit 1#1)))
                                      else (pure (())))
                                  else
                                    (do
                                      if ((questionMark == PMU_EVENT_L2D_CACHE_LMISS_RD) : Bool)
                                      then
                                        (do
                                          let w__18 ← (( do (HaveStatisticalProfilingv1p4 ()) ) :
                                            SailME Unit Bool )
                                          if (w__18 : Bool)
                                          then
                                            (do
                                              let w__19 ← (( do readReg SPESampleEvents ) : SailME
                                                Unit (BitVec 64) )
                                              writeReg SPESampleEvents (BitVec.update w__19 20
                                                (Bit 1#1)))
                                          else (pure (())))
                                      else
                                        (do
                                          if ((questionMark == PMU_EVENT_L2D_CACHE_RD) : Bool)
                                          then
                                            (do
                                              let w__20 ← (( do (HaveStatisticalProfilingv1p4 ())
                                                ) : SailME Unit Bool )
                                              if (w__20 : Bool)
                                              then
                                                (do
                                                  let w__21 ← (( do readReg SPESampleEvents ) :
                                                    SailME Unit (BitVec 64) )
                                                  writeReg SPESampleEvents (BitVec.update w__21 19
                                                    (Bit 1#1)))
                                              else (pure (())))
                                          else
                                            (do
                                              if ((questionMark == PMU_EVENT_SVE_PRED_EMPTY_SPEC) : Bool)
                                              then
                                                (do
                                                  let w__22 ← (( do
                                                    (HaveStatisticalProfilingv1p1 ()) ) : SailME
                                                    Unit Bool )
                                                  if (w__22 : Bool)
                                                  then
                                                    (do
                                                      let w__23 ← (( do readReg SPESampleEvents )
                                                        : SailME Unit (BitVec 64) )
                                                      writeReg SPESampleEvents (BitVec.update w__23
                                                        18 (Bit 1#1)))
                                                  else (pure (())))
                                              else
                                                (do
                                                  if ((questionMark == PMU_EVENT_SVE_PRED_PARTIAL_SPEC) : Bool)
                                                  then
                                                    (do
                                                      let w__24 ← (( do
                                                        (HaveStatisticalProfilingv1p1 ()) ) : SailME
                                                        Unit Bool )
                                                      if (w__24 : Bool)
                                                      then
                                                        (do
                                                          let w__25 ← (( do
                                                            readReg SPESampleEvents ) : SailME Unit
                                                            (BitVec 64) )
                                                          writeReg SPESampleEvents (BitVec.update
                                                            w__25 17 (Bit 1#1)))
                                                      else (pure (())))
                                                  else
                                                    (do
                                                      if ((questionMark == PMU_EVENT_LDST_ALIGN_LAT) : Bool)
                                                      then
                                                        (do
                                                          let w__26 ← (( do
                                                            (HaveStatisticalProfilingv1p1 ()) ) :
                                                            SailME Unit Bool )
                                                          if (w__26 : Bool)
                                                          then
                                                            (do
                                                              let w__27 ← (( do
                                                                readReg SPESampleEvents ) : SailME
                                                                Unit (BitVec 64) )
                                                              writeReg SPESampleEvents (BitVec.update
                                                                w__27 11 (Bit 1#1)))
                                                          else (pure (())))
                                                      else
                                                        (do
                                                          if ((questionMark == PMU_EVENT_REMOTE_ACCESS) : Bool)
                                                          then
                                                            (do
                                                              let w__28 ← (( do
                                                                readReg SPESampleEvents ) : SailME
                                                                Unit (BitVec 64) )
                                                              writeReg SPESampleEvents (BitVec.update
                                                                w__28 10 (Bit 1#1)))
                                                          else
                                                            (do
                                                              if ((questionMark == PMU_EVENT_LL_CACHE_MISS) : Bool)
                                                              then
                                                                (do
                                                                  let w__29 ← (( do
                                                                    readReg SPESampleEvents ) :
                                                                    SailME Unit (BitVec 64) )
                                                                  writeReg SPESampleEvents (BitVec.update
                                                                    w__29 9 (Bit 1#1)))
                                                              else
                                                                (do
                                                                  if ((questionMark == PMU_EVENT_LL_CACHE) : Bool)
                                                                  then
                                                                    (do
                                                                      let w__30 ← (( do
                                                                        readReg SPESampleEvents ) :
                                                                        SailME Unit (BitVec 64) )
                                                                      writeReg SPESampleEvents (BitVec.update
                                                                        w__30 8 (Bit 1#1)))
                                                                  else
                                                                    (do
                                                                      if ((questionMark == PMU_EVENT_BR_MIS_PRED) : Bool)
                                                                      then
                                                                        (do
                                                                          let w__31 ← (( do
                                                                            readReg SPESampleEvents
                                                                            ) : SailME Unit
                                                                            (BitVec 64) )
                                                                          writeReg SPESampleEvents (BitVec.update
                                                                            w__31 7 (Bit 1#1)))
                                                                      else
                                                                        (do
                                                                          if ((questionMark == PMU_EVENT_BR_MIS_PRED_RETIRED) : Bool)
                                                                          then
                                                                            (do
                                                                              let w__32 ← (( do
                                                                                readReg SPESampleEvents
                                                                                ) : SailME Unit
                                                                                (BitVec 64) )
                                                                              writeReg SPESampleEvents (BitVec.update
                                                                                w__32 7 (Bit 1#1)))
                                                                          else
                                                                            (do
                                                                              if ((questionMark == PMU_EVENT_DTLB_WALK) : Bool)
                                                                              then
                                                                                (do
                                                                                  let w__33 ← (( do
                                                                                    readReg SPESampleEvents
                                                                                    ) : SailME Unit
                                                                                    (BitVec 64) )
                                                                                  writeReg SPESampleEvents (BitVec.update
                                                                                    w__33 5
                                                                                    (Bit 1#1)))
                                                                              else
                                                                                (do
                                                                                  if ((questionMark == PMU_EVENT_L1D_TLB) : Bool)
                                                                                  then
                                                                                    (do
                                                                                      let w__34 ← (( do
                                                                                        readReg SPESampleEvents
                                                                                        ) : SailME
                                                                                        Unit
                                                                                        (BitVec 64)
                                                                                        )
                                                                                      writeReg SPESampleEvents (BitVec.update
                                                                                        w__34 4
                                                                                        (Bit 1#1)))
                                                                                  else
                                                                                    (do
                                                                                      if ((questionMark == PMU_EVENT_L1D_CACHE_REFILL) : Bool)
                                                                                      then
                                                                                        (do
                                                                                          let w__35 ← (( do
                                                                                            (HaveStatisticalProfilingv1p4
                                                                                              ()) )
                                                                                            : SailME
                                                                                            Unit
                                                                                            Bool )
                                                                                          if ((! w__35) : Bool)
                                                                                          then
                                                                                            (do
                                                                                              let w__36 ← (( do
                                                                                                readReg SPESampleEvents
                                                                                                ) :
                                                                                                SailME
                                                                                                Unit
                                                                                                (BitVec 64)
                                                                                                )
                                                                                              writeReg SPESampleEvents (BitVec.update
                                                                                                w__36
                                                                                                3
                                                                                                (Bit
                                                                                                  1#1)))
                                                                                          else
                                                                                            (pure (())))
                                                                                      else
                                                                                        (do
                                                                                          if ((questionMark == PMU_EVENT_L1D_CACHE_LMISS_RD) : Bool)
                                                                                          then
                                                                                            (do
                                                                                              let w__37 ← (( do
                                                                                                (HaveStatisticalProfilingv1p4
                                                                                                  ())
                                                                                                ) :
                                                                                                SailME
                                                                                                Unit
                                                                                                Bool
                                                                                                )
                                                                                              if (w__37 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  let w__38 ← (( do
                                                                                                    readReg SPESampleEvents
                                                                                                    )
                                                                                                    :
                                                                                                    SailME
                                                                                                    Unit
                                                                                                    (BitVec 64)
                                                                                                    )
                                                                                                  writeReg SPESampleEvents (BitVec.update
                                                                                                    w__38
                                                                                                    3
                                                                                                    (Bit
                                                                                                      1#1)))
                                                                                              else
                                                                                                (pure (())))
                                                                                          else
                                                                                            (do
                                                                                              if ((questionMark == PMU_EVENT_L1D_CACHE) : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  let w__39 ← (( do
                                                                                                    readReg SPESampleEvents
                                                                                                    )
                                                                                                    :
                                                                                                    SailME
                                                                                                    Unit
                                                                                                    (BitVec 64)
                                                                                                    )
                                                                                                  writeReg SPESampleEvents (BitVec.update
                                                                                                    w__39
                                                                                                    2
                                                                                                    (Bit
                                                                                                      1#1)))
                                                                                              else
                                                                                                (do
                                                                                                  if ((questionMark == PMU_EVENT_INST_RETIRED) : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      let w__40 ← (( do
                                                                                                        readReg SPESampleEvents
                                                                                                        )
                                                                                                        :
                                                                                                        SailME
                                                                                                        Unit
                                                                                                        (BitVec 64)
                                                                                                        )
                                                                                                      writeReg SPESampleEvents (BitVec.update
                                                                                                        w__40
                                                                                                        1
                                                                                                        (Bit
                                                                                                          1#1)))
                                                                                                  else
                                                                                                    (do
                                                                                                      if ((questionMark == PMU_EVENT_EXC_TAKEN) : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          let w__41 ← (( do
                                                                                                            readReg SPESampleEvents
                                                                                                            )
                                                                                                            :
                                                                                                            SailME
                                                                                                            Unit
                                                                                                            (BitVec 64)
                                                                                                            )
                                                                                                          writeReg SPESampleEvents (BitVec.update
                                                                                                            w__41
                                                                                                            0
                                                                                                            (Bit
                                                                                                              1#1)))
                                                                                                      else
                                                                                                        (do
                                                                                                          SailME.throw (() : Unit)))))))))))))))))))))))))))


end ArmFull.Functions
