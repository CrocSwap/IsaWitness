import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0020
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0042
import ArmFull.Fn.M0051
import ArmFull.Fn.M0054
import ArmFull.Fn.M0059
import ArmFull.Fn.M0061
import ArmFull.Fn.M0087
import ArmFull.Fn.M0092
import ArmFull.Fn.M0123
import ArmFull.Fn.M0144
import ArmFull.Fn.M0149
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0186
import ArmFull.Fn.M0202
import ArmFull.Fn.M0254
import ArmFull.Fn.M0260
import ArmFull.Fn.M1002
import ArmFull.Fn.M1003

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

def SPEConstructRecord (_ : Unit) : SailM Unit := do
  let payload_size ← (( do (undefined_int_at (.site 2446) ()) ) : SailM Int )
  (SPEEmptyRecord ())
  let w__0 ← (( do readReg SPESampleContextEL1Valid ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do readReg SPESampleContextEL1 ) : SailM (BitVec 32) )
      (SPEAddPacketToRecord 0b01#2 0b0100#4 w__1))
  else (pure (()))
  let w__2 ← (( do readReg SPESampleContextEL2Valid ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let w__3 ← (( do readReg SPESampleContextEL2 ) : SailM (BitVec 32) )
      (SPEAddPacketToRecord 0b01#2 0b0101#4 w__3))
  else (pure (()))
  let loop_counter_index_lower : Nat := 0
  let loop_counter_index_upper : Nat := (Sail.Int.toNatChecked ((SPEMaxCounters -i 1)))
  (do
    let mut loop_vars := ()
    for counter_index in [loop_counter_index_lower:loop_counter_index_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__4 ← (( do readReg SPESampleCounterValid ) : SailM (Vector Bool 32) )
        if ((GetElem?.getElem! w__4 (Sail.Int.toNatChecked (counter_index))) : Bool)
        then
          (do
            if ((counter_index ≥b 8) : Bool)
            then
              (do
                (SPEAddByteToRecord (0b001000#6 +++ (integer_subrange counter_index 4 3))))
            else (pure (()))
            let large_counters ← (( do (__IMPDEF_boolean "SPE 16bit counters") ) : SailM Bool )
            let w__6 ← (( do
              (pure ((← do
                    let w__5 ← (( do readReg SPESampleCounter ) : SailM (Vector Int 32) )
                    (pure ((((GetElem?.getElem! w__5 (Sail.Int.toNatChecked (counter_index))) >b (BitVec.toNat
                          0xFFFF#16)) : Bool)))) && large_counters)) ) : SailM Bool )
            if (w__6 : Bool)
            then
              (do
                let w__7 ← (( do readReg SPESampleCounter ) : SailM (Vector Int 32) )
                writeReg SPESampleCounter (vectorUpdate w__7 (Sail.Int.toNatChecked (counter_index))
                  (BitVec.toNat 0xFFFF#16)))
            else
              (do
                let w__8 ← (( do readReg SPESampleCounter ) : SailM (Vector Int 32) )
                if (((GetElem?.getElem! w__8 (Sail.Int.toNatChecked (counter_index))) >b (BitVec.toNat
                       0xFFF#12)) : Bool)
                then
                  (do
                    let w__9 ← (( do readReg SPESampleCounter ) : SailM (Vector Int 32) )
                    writeReg SPESampleCounter (vectorUpdate w__9
                      (Sail.Int.toNatChecked (counter_index)) (BitVec.toNat 0xFFF#12)))
                else (pure (())))
            let w__10 ← (( do readReg SPESampleCounter ) : SailM (Vector Int 32) )
            (SPEAddPacketToRecord 0b10#2 (1#1 +++ (integer_subrange counter_index 2 0))
              (integer_subrange (GetElem?.getElem! w__10 (Sail.Int.toNatChecked (counter_index))) 15
                0)))
        else (pure (()))
    (pure loop_vars))
  let w__11 ← (( do (HaveStatisticalProfilingv1p2 ()) ) : SailM Bool )
  if (w__11 : Bool)
  then
    (do
      let include_prev_br_name ← (( do (__IMPDEF_boolean "SPE get prev br if not br") ) : SailM
        Bool )
      let w__13 ← (( do
        (pure ((← do
              let w__12 ← (( do readReg SPESampleOpType ) : SailM OpType )
              (pure (((bne w__12 OpType_Branch) : Bool)))) && (! include_prev_br_name))) ) : SailM
        Bool )
      if (w__13 : Bool)
      then
        (do
          let w__14 ← (( do readReg SPESampleAddressValid ) : SailM (Vector Bool 32) )
          writeReg SPESampleAddressValid (vectorUpdate w__14 SPEAddrPosPrevBranchTarget false))
      else (pure (())))
  else (pure (()))
  let w__17 ← (( do
    if ((← do
         let w__15 ← (( do (StatisticalProfilingEnabled__1 EL2) ) : SailM Bool )
         (pure (((! w__15) : Bool)))) : Bool)
    then
      (do
        readReg SPESampleInstIsNV2)
    else (pure false) ) : SailM Bool )
  if (w__17 : Bool)
  then
    (do
      let w__18 ← (( do readReg SPESampleAddressValid ) : SailM (Vector Bool 32) )
      writeReg SPESampleAddressValid (vectorUpdate w__18 SPEAddrPosDataVirtual false))
  else (pure (()))
  let loop_address_index_lower : Nat := 0
  let loop_address_index_upper : Nat := (Sail.Int.toNatChecked ((SPEMaxAddrs -i 1)))
  (do
    let mut loop_vars := ()
    for address_index in [loop_address_index_lower:loop_address_index_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__19 ← (( do readReg SPESampleAddressValid ) : SailM (Vector Bool 32) )
        if ((GetElem?.getElem! w__19 (Sail.Int.toNatChecked (address_index))) : Bool)
        then
          (do
            if ((address_index ≥b 8) : Bool)
            then
              (do
                (SPEAddByteToRecord (0b001000#6 +++ (integer_subrange address_index 4 3))))
            else (pure (()))
            let w__20 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
            (SPEAddPacketToRecord 0b10#2 (0#1 +++ (integer_subrange address_index 2 0))
              (GetElem?.getElem! w__20 (Sail.Int.toNatChecked (address_index)))))
        else (pure (()))
    (pure loop_vars))
  let w__21 ← (( do readReg SPESampleDataSourceValid ) : SailM Bool )
  let payload_size ← (( do
    if (w__21 : Bool)
    then
      (do
        let w__22 ← (( do (SPEGetDataSourcePayloadSize ()) ) : SailM Int )
        let payload_size : Int := (w__22 : Int)
        let payload_size : Int := payload_size
        ArmFull.assert ((0 ≤b ((8 *i payload_size) -i 1)) && (((8 *i payload_size) -i 1) <b 16)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:35364.84-35364.85"
        let w__23 ← (( do readReg SPESampleDataSource ) : SailM (BitVec 16) )
        (SPEAddPacketToRecord 0b01#2 0b0011#4
          (Sail.BitVec.extractLsb w__23 (Sail.Int.toNatChecked (((8 *i payload_size) -i 1))) 0))
        (pure (payload_size)))
    else (pure (payload_size)) ) : SailM Int )
  let w__24 ← (( do readReg SPESampleClass ) : SailM (BitVec 2) )
  let w__25 ← (( do readReg SPESampleSubclass ) : SailM (BitVec 8) )
  (SPEAddPacketToRecord 0b01#2 (0b10#2 +++ w__24) w__25)
  let payload_size ← (( do (SPEGetEventsPayloadSize ()) ) : SailM Int )
  ArmFull.assert ((0 ≤b ((8 *i payload_size) -i 1)) && (((8 *i payload_size) -i 1) <b 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:35369.80-35369.81"
  ArmFull.assert ((((((8 *i payload_size) -i 1) -i 0) +i 1) == 8) || ((((((8 *i payload_size) -i 1) -i 0) +i 1) == 16) || ((((((8 *i payload_size) -i 1) -i 0) +i 1) == 32) || (((((8 *i payload_size) -i 1) -i 0) +i 1) == 64)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:35370.173-35370.174"
  let w__26 ← (( do readReg SPESampleEvents ) : SailM (BitVec 64) )
  (SPEAddPacketToRecord 0b01#2 0b0010#4
    (Sail.BitVec.extractLsb w__26 (Sail.Int.toNatChecked (((8 *i payload_size) -i 1))) 0))
  let w__27 ← (( do readReg SPESampleTimestampValid ) : SailM Bool )
  if (w__27 : Bool)
  then
    (do
      let w__28 ← (( do readReg SPESampleTimestamp ) : SailM (BitVec 64) )
      (SPEAddPacketToRecord 0b01#2 0b0001#4 w__28))
  else
    (do
      (SPEAddByteToRecord 0b00000001#8))
  let loop_vars ← sailWhileFuelM (fuel := 1048576) (fun () => do
      let w__29 ← (( do readReg SPERecordSize ) : SailM Int )
      let w__30 ← (( do readReg PMBIDR_EL1 ) : SailM (BitVec 64) )
      (pure ((((fmod_int w__29 (Int.shiftl 1 (BitVec.toNat (_get_PMBIDR_EL1_Type_Align w__30)))) != 0) : Bool)))) ()
    fun () => do (SPEAddByteToRecord (Zeros (n := 8)))
  (pure loop_vars)
  (SPEWriteToBuffer ())


def AArch32_IC (opscope : CacheOpScope) : SailM Unit := do
  let regval ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  (AArch32_IC__1 regval opscope)


/-- Type quantifiers: k_aligned : Bool, size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def AArch32_MemSingle_read (address : (BitVec 32)) (size : Nat) (accdesc : AccessDescriptor) (aligned : Bool) : SailM (BitVec (size * 8)) := do
  let ispair : Bool := false
  ((Sail.BitVec.castWidth ) <$> (AArch32_MemSingle_read__1 address size accdesc aligned ispair))


/-- Type quantifiers: k_aligned : Bool, size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def AArch32_MemSingle_set (address : (BitVec 32)) (size : Nat) (accdesc : AccessDescriptor) (aligned : Bool) (value_name : (BitVec (size * 8))) : SailM Unit := do
  let ispair : Bool := false
  (AArch32_MemSingle_set__1 address size accdesc aligned ispair (Sail.BitVec.castWidth value_name))


/-- Type quantifiers: t : Int -/
def IC_IALLUIS_SysOpsWrite_3eb8cc845c2f9444 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TPU : (BitVec 1) := (_get_HCR_EL2_Type_TPU w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TICAB : (BitVec 1) := (_get_HCR_EL2_Type_TICAB w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_ICIALLUIS : (BitVec 1) := (_get_HFGITR_EL2_Type_ICIALLUIS w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__6 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TPU == 1#1) : Bool))) ) : SailM Bool )
          if (w__6 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__8 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TICAB == 1#1) : Bool))) ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__13 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_ICIALLUIS == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__13 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      (AArch64_IC CacheOpScope_ALLUIS)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              (AArch64_IC CacheOpScope_ALLUIS))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  (AArch64_IC CacheOpScope_ALLUIS))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def IC_IALLU_SysOpsWrite_11cf556c15dd6d58 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TPU : (BitVec 1) := (_get_HCR_EL2_Type_TPU w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TOCU : (BitVec 1) := (_get_HCR_EL2_Type_TOCU w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_ICIALLU : (BitVec 1) := (_get_HFGITR_EL2_Type_ICIALLU w__4)
  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_FB : (BitVec 1) := (_get_HCR_EL2_Type_FB w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__7 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TPU == 1#1) : Bool))) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__9 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TOCU == 1#1) : Bool))) ) : SailM Bool )
              if (w__9 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__14 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_ICIALLU == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__14 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__16 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__HCR_EL2_FB == 1#1) : Bool))) ) : SailM Bool )
                      if (w__16 : Bool)
                      then
                        (do
                          (AArch64_IC CacheOpScope_ALLUIS))
                      else
                        (do
                          (AArch64_IC CacheOpScope_ALLU))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              (AArch64_IC CacheOpScope_ALLU))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  (AArch64_IC CacheOpScope_ALLU))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DCCIMVAC_SysRegWrite32_9ec7bae67091217f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T7 : (BitVec 1) := (_get_HSTR_EL2_Type_T7 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T7 : (BitVec 1) := (_get_HSTR_Type_T7 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TPCP : (BitVec 1) := (_get_HCR_EL2_Type_TPCP w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TPC : (BitVec 1) := (_get_HCR_Type_TPC w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__8 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__6) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__12 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__16 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__14 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__14) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TPCP == 1#1) : Bool))) ) : SailM Bool )
                  if (w__16 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__20 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TPC == 1#1) : Bool))) ) : SailM Bool )
                      if (w__20 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__21 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (AArch32_DC w__21 CacheOp_CleanInvalidate CacheOpScope_PoC))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__22 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AArch32_DC w__22 CacheOp_CleanInvalidate CacheOpScope_PoC))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__23 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AArch32_DC w__23 CacheOp_CleanInvalidate CacheOpScope_PoC))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DCCISW_SysRegWrite32_419e334023bc59ed (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T7 : (BitVec 1) := (_get_HSTR_EL2_Type_T7 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T7 : (BitVec 1) := (_get_HSTR_Type_T7 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TSW : (BitVec 1) := (_get_HCR_EL2_Type_TSW w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TSW : (BitVec 1) := (_get_HCR_Type_TSW w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__8 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__6) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__12 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__16 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__14 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__14) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TSW == 1#1) : Bool))) ) : SailM Bool )
                  if (w__16 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__20 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TSW == 1#1) : Bool))) ) : SailM Bool )
                      if (w__20 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__21 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (AArch32_DC w__21 CacheOp_CleanInvalidate CacheOpScope_SetWay))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__22 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AArch32_DC w__22 CacheOp_CleanInvalidate CacheOpScope_SetWay))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__23 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AArch32_DC w__23 CacheOp_CleanInvalidate CacheOpScope_SetWay))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DCCMVAC_SysRegWrite32_acc09968a78b7280 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T7 : (BitVec 1) := (_get_HSTR_EL2_Type_T7 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T7 : (BitVec 1) := (_get_HSTR_Type_T7 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TPCP : (BitVec 1) := (_get_HCR_EL2_Type_TPCP w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TPC : (BitVec 1) := (_get_HCR_Type_TPC w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__8 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__6) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__12 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__16 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__14 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__14) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TPCP == 1#1) : Bool))) ) : SailM Bool )
                  if (w__16 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__20 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TPC == 1#1) : Bool))) ) : SailM Bool )
                      if (w__20 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__21 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (AArch32_DC w__21 CacheOp_Clean CacheOpScope_PoC))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__22 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AArch32_DC w__22 CacheOp_Clean CacheOpScope_PoC))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__23 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AArch32_DC w__23 CacheOp_Clean CacheOpScope_PoC))
              else (pure (())))))


end ArmFull.Functions
