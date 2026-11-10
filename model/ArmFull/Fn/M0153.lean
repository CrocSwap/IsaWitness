import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0008
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0024
import ArmFull.Fn.M0041
import ArmFull.Fn.M0087
import ArmFull.Fn.M0092
import ArmFull.Fn.M0111
import ArmFull.Fn.M0144

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

def UsingAArch32 (_ : Unit) : SailM Bool := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let aarch32 : Bool := (w__0.nRW == 1#1)
  if ((! (HaveAArch32 ())) : Bool)
  then
    (do
      ArmFull.assert (! aarch32) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:4029.32-4029.33")
  else (pure (()))
  let w__1 ← (( do (HaveAArch64 ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then
    (do
      ArmFull.assert aarch32 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:4032.22-4032.23")
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


/-- Type quantifiers: i : Int -/
def C27bSimpleAllowed (which : Unpredictable) (i : Int) : SailM Bool := do
  if ((BEq.beq which Unpredictable_EL2TIMESTAMP) : Bool)
  then
    if ((i != 2) : Bool)
    then (pure true)
    else
      (do
        (HaveECVExt ()))
  else
    (do
      if ((BEq.beq which Unpredictable_EL1TIMESTAMP) : Bool)
      then
        if ((i != 0) : Bool)
        then
          if ((i != 2) : Bool)
          then (pure true)
          else
            (do
              (HaveECVExt ()))
        else (pure false)
      else
        (do
          if ((BEq.beq which Unpredictable_RESERVEDNSxB) : Bool)
          then
            if ((i != 4) : Bool)
            then
              if ((i != 5) : Bool)
              then
                (pure ((← do
                      (HaveSecureEL2Ext ())) || (i ≥b 2)))
              else (pure false)
            else (pure false)
          else
            (do
              if ((BEq.beq which Unpredictable_RESTCF) : Bool)
              then
                if ((i != 3) : Bool)
                then (pure true)
                else
                  (do
                    (HaveMTEAsymFaultExt ()))
              else
                (do
                  if ((BEq.beq which Unpredictable_PMSCR_PCT) : Bool)
                  then
                    if ((i != 2) : Bool)
                    then
                      if ((i != 3) : Bool)
                      then (pure true)
                      else
                        (do
                          (HaveECVExt ()))
                    else (pure false)
                  else
                    (pure (if ((BEq.beq which Unpredictable_RESDACR) : Bool)
                      then (i != 2)
                      else
                        (if ((BEq.beq which Unpredictable_RESTEXCB) : Bool)
                        then ((i != 5) && ((i <b 9) || (i ≥b 16)))
                        else
                          (if ((BEq.beq which Unpredictable_RESPRRR) : Bool)
                          then (i != 3)
                          else true))))))))


def EffectiveSCR_EL3_RW (_ : Unit) : SailM (BitVec 1) := SailME.run do
  let w__0 ← (( do (HaveAArch64 ()) ) : SailME (BitVec 1) Bool )
  if ((! w__0) : Bool)
  then (pure (0#1))
  else
    (do
      if (((! (HaveAArch32EL EL2)) && (! (HaveAArch32EL EL1))) : Bool)
      then (pure (1#1))
      else
        (do
          if ((HaveAArch32EL EL1) : Bool)
          then
            (do
              let w__2 ← (( do
                if (((! (HaveAArch32EL EL2)) : Bool) : Bool)
                then
                  (do
                    let w__1 ← (( do readReg SCR_EL3 ) : SailME (BitVec 1) (BitVec 64) )
                    (pure ((((_get_SCR_EL3_Type_NS w__1) == 1#1) : Bool))))
                else (pure false) ) : SailME (BitVec 1) Bool )
              if (w__2 : Bool)
              then
                (do
                  SailME.throw (1#1 : (BitVec 1)))
              else
                (do
                  let w__7 ← (( do
                    if ((← do
                         if ((← do
                              (HaveSecureEL2Ext ())) : Bool)
                         then
                           (do
                             let w__4 ← (( do readReg SCR_EL3 ) : SailME (BitVec 1) (BitVec 64) )
                             (pure ((((_get_SCR_EL3_Type_EEL2 w__4) == 1#1) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__6 ← (( do readReg SCR_EL3 ) : SailME (BitVec 1) (BitVec 64) )
                        (pure ((((_get_SCR_EL3_Type_NS w__6) == 0#1) : Bool))))
                    else (pure false) ) : SailME (BitVec 1) Bool )
                  if (w__7 : Bool)
                  then
                    (do
                      SailME.throw (1#1 : (BitVec 1)))
                  else (pure (()))))
          else (pure (()))
          let w__8 ← (( do readReg SCR_EL3 ) : SailME (BitVec 1) (BitVec 64) )
          (pure ((_get_SCR_EL3_Type_RW w__8)))))


def ExternalRealmInvasiveDebugEnabled (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (HaveRME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      if ((← do
           (ExternalInvasiveDebugEnabled ())) : Bool)
      then
        (do
          let w__2 ← (( do readReg RLPIDEN ) : SailM Signal )
          (pure (((BEq.beq w__2 Signal_High) : Bool))))
      else (pure false))


/-- Type quantifiers: nbits_in : Int -/
def ImplementedSVEVectorLength (nbits_in : Int) : SailM Int := SailME.run do
  let maxbits : Int := (MaxImplementedVL ())
  let w__1 ← (( do
    if ((((128 ≤b maxbits) && (maxbits ≤b 2048)) : Bool) : Bool)
    then
      (do
        (IsPow2 maxbits))
    else (pure false) ) : SailME Int Bool )
  ArmFull.assert w__1 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:6873.63-6873.64"
  let nbits : Int := (Min.min nbits_in maxbits)
  ArmFull.assert (((128 ≤b nbits) && (nbits ≤b 2048)) && ((Align_int nbits 128) == nbits)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:6875.70-6875.71"
  let nbits ← (( do
    let loop_vars ← sailWhileFuelM (α := Int) (fuel := 1048576) (fun nbits => (pure (nbits >b 128))) nbits
      fun nbits => do
        let w__2 ← (( do (IsPow2 nbits) ) : SailME Int Bool )
        if (w__2 : Bool)
        then
          (do
            let nbits : Int := nbits
            ArmFull.assert (((((nbits == 128) || (nbits == 256)) || (nbits == 512)) || (nbits == 1024)) || (nbits == 2048)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:6879.44-6879.45"
            SailME.throw (nbits : Int)
            (pure (nbits)))
        else
          (let nbits : Int := (nbits -i 128)
          (pure (nbits)))
    (pure loop_vars) ) : SailME Int Int )
  let nbits : Int := nbits
  ArmFull.assert (((((nbits == 128) || (nbits == 256)) || (nbits == 512)) || (nbits == 1024)) || (nbits == 2048)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:6885.36-6885.37"
  (pure (nbits))


/-- Type quantifiers: nbits_in : Int -/
def ImplementedSMEVectorLength (nbits_in : Int) : SailM Int := SailME.run do
  let maxbits ← (( do (MaxImplementedSVL ()) ) : SailME Int Int )
  ArmFull.assert (((((maxbits == 128) || (maxbits == 256)) || (maxbits == 512)) || (maxbits == 1024)) || (maxbits == 2048)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:6932.38-6932.39"
  let nbits : Int := (Min.min nbits_in maxbits)
  ArmFull.assert (((128 ≤b nbits) && (nbits ≤b 2048)) && ((Align_int nbits 128) == nbits)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:6934.70-6934.71"
  let nbits ← (( do
    let loop_vars ← sailWhileFuelM (α := Int) (fuel := 1048576) (fun nbits => (pure (nbits >b 128))) nbits
      fun nbits => do
        let w__1 ← (( do
          (pure ((← do
                (IsPow2 nbits)) && ((SupportedPowerTwoSVL nbits) : Bool))) ) : SailME Int Bool )
        if (w__1 : Bool)
        then
          (do
            let nbits : Int := nbits
            ArmFull.assert (((((nbits == 128) || (nbits == 256)) || (nbits == 512)) || (nbits == 1024)) || (nbits == 2048)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:6938.44-6938.45"
            SailME.throw (nbits : Int)
            (pure (nbits)))
        else
          (let nbits : Int := (nbits -i 128)
          (pure (nbits)))
    (pure loop_vars) ) : SailME Int Int )
  let nbits : Int := 128
  let nbits ← (( do
    let loop_vars_1 ← sailWhileFuelM (α := Int) (fuel := 1048576) (fun nbits => (pure (nbits <b maxbits))) nbits
      fun nbits => do
        if ((SupportedPowerTwoSVL nbits) : Bool)
        then
          (do
            let nbits : Int := nbits
            ArmFull.assert (((((nbits == 128) || (nbits == 256)) || (nbits == 512)) || (nbits == 1024)) || (nbits == 2048)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:6947.44-6947.45"
            SailME.throw (nbits : Int)
            (pure (nbits)))
        else
          (let nbits : Int := (nbits *i 2)
          (pure (nbits)))
    (pure loop_vars_1) ) : SailME Int Int )
  (pure (maxbits))


end ArmFull.Functions
