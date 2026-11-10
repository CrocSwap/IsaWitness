import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0008
import ArmFull.Fn.M0009
import ArmFull.Fn.M0015
import ArmFull.Fn.M0016
import ArmFull.Fn.M0019
import ArmFull.Fn.M0020
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0035
import ArmFull.Fn.M0036
import ArmFull.Fn.M0038
import ArmFull.Fn.M0039
import ArmFull.Fn.M0040
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0044
import ArmFull.Fn.M0045
import ArmFull.Fn.M0046
import ArmFull.Fn.M0047
import ArmFull.Fn.M0048
import ArmFull.Fn.M0049
import ArmFull.Fn.M0050
import ArmFull.Fn.M0051
import ArmFull.Fn.M0052
import ArmFull.Fn.M0053
import ArmFull.Fn.M0054
import ArmFull.Fn.M0055
import ArmFull.Fn.M0056
import ArmFull.Fn.M0057
import ArmFull.Fn.M0058
import ArmFull.Fn.M0059
import ArmFull.Fn.M0061
import ArmFull.Fn.M0062
import ArmFull.Fn.M0063
import ArmFull.Fn.M0065
import ArmFull.Fn.M0069
import ArmFull.Fn.M0070
import ArmFull.Fn.M0071
import ArmFull.Fn.M0072
import ArmFull.Fn.M0074
import ArmFull.Fn.M0076
import ArmFull.Fn.M0079
import ArmFull.Fn.M0080
import ArmFull.Fn.M0081
import ArmFull.Fn.M0082
import ArmFull.Fn.M0086

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

/-- Type quantifiers: t : Int -/
def ICH_AP0R_SysRegWrite32_0687237dd975d38e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T12 : (BitVec 1) := (_get_HSTR_EL2_Type_T12 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T12 : (BitVec 1) := (_get_HSTR_Type_T12 w__2)
  let w__3 ← (( do (ICC_HSRE_read ()) ) : SailM (BitVec 32) )
  let __ICC_HSRE_SRE : (BitVec 1) := (_get_ICC_HSRE_Type_SRE w__3)
  let w__4 ← (( do readReg ICC_MSRE ) : SailM (BitVec 32) )
  let __ICC_MSRE_SRE : (BitVec 1) := (_get_ICC_MSRE_Type_SRE w__4)
  sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def ICH_AP0R_SysRegWrite32_e8bf01c9f2e53161 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T12 : (BitVec 1) := (_get_HSTR_EL2_Type_T12 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T12 : (BitVec 1) := (_get_HSTR_Type_T12 w__2)
  let w__3 ← (( do (ICC_HSRE_read ()) ) : SailM (BitVec 32) )
  let __ICC_HSRE_SRE : (BitVec 1) := (_get_ICC_HSRE_Type_SRE w__3)
  let w__4 ← (( do readReg ICC_MSRE ) : SailM (BitVec 32) )
  let __ICC_MSRE_SRE : (BitVec 1) := (_get_ICC_MSRE_Type_SRE w__4)
  sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def ICH_AP0R_SysRegWrite32_e8e0b6211baf6183 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T12 : (BitVec 1) := (_get_HSTR_EL2_Type_T12 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T12 : (BitVec 1) := (_get_HSTR_Type_T12 w__2)
  let w__3 ← (( do (ICC_HSRE_read ()) ) : SailM (BitVec 32) )
  let __ICC_HSRE_SRE : (BitVec 1) := (_get_ICC_HSRE_Type_SRE w__3)
  let w__4 ← (( do readReg ICC_MSRE ) : SailM (BitVec 32) )
  let __ICC_MSRE_SRE : (BitVec 1) := (_get_ICC_MSRE_Type_SRE w__4)
  sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def ICH_AP1R_SysRegWrite32_100dab3ceee19d37 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T12 : (BitVec 1) := (_get_HSTR_EL2_Type_T12 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T12 : (BitVec 1) := (_get_HSTR_Type_T12 w__2)
  let w__3 ← (( do (ICC_HSRE_read ()) ) : SailM (BitVec 32) )
  let __ICC_HSRE_SRE : (BitVec 1) := (_get_ICC_HSRE_Type_SRE w__3)
  let w__4 ← (( do readReg ICC_MSRE ) : SailM (BitVec 32) )
  let __ICC_MSRE_SRE : (BitVec 1) := (_get_ICC_MSRE_Type_SRE w__4)
  sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def ICH_AP1R_SysRegWrite32_4eff4ec729dbfa39 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T12 : (BitVec 1) := (_get_HSTR_EL2_Type_T12 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T12 : (BitVec 1) := (_get_HSTR_Type_T12 w__2)
  let w__3 ← (( do (ICC_HSRE_read ()) ) : SailM (BitVec 32) )
  let __ICC_HSRE_SRE : (BitVec 1) := (_get_ICC_HSRE_Type_SRE w__3)
  let w__4 ← (( do readReg ICC_MSRE ) : SailM (BitVec 32) )
  let __ICC_MSRE_SRE : (BitVec 1) := (_get_ICC_MSRE_Type_SRE w__4)
  sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def ICH_AP1R_SysRegWrite32_9d0709acdf26e0db (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T12 : (BitVec 1) := (_get_HSTR_EL2_Type_T12 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T12 : (BitVec 1) := (_get_HSTR_Type_T12 w__2)
  let w__3 ← (( do (ICC_HSRE_read ()) ) : SailM (BitVec 32) )
  let __ICC_HSRE_SRE : (BitVec 1) := (_get_ICC_HSRE_Type_SRE w__3)
  let w__4 ← (( do readReg ICC_MSRE ) : SailM (BitVec 32) )
  let __ICC_MSRE_SRE : (BitVec 1) := (_get_ICC_MSRE_Type_SRE w__4)
  sailThrow ((Error_Undefined ()))


def execute_aarch32_instrs_CLREX_Op_A_txt (_ : Unit) : Unit :=
  (ClearExclusiveLocal (ProcessorID ()))


def execute_aarch32_instrs_ISB_Op_A_txt (_ : Unit) : SailM Unit := do
  (InstructionSynchronizationBarrier ())


def execute_aarch32_instrs_SB_Op_A_txt (_ : Unit) : SailM Unit := do
  (SpeculationBarrier ())


def execute_aarch32_instrs_SEV_Op_A_txt (_ : Unit) : Unit :=
  (SendEvent ())


def execute_aarch32_instrs_YIELD_Op_A_txt (_ : Unit) : Unit :=
  (Hint_Yield ())


def execute_aarch32_instrs_SEVL_Op_A_txt (_ : Unit) : SailM Unit := do
  (SendEventLocal ())


def execute_aarch32_instrs_SETPAN_Op_A_txt (value_name : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.EL != EL0) : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with PAN := value_name })
  else (pure (()))


def execute_aarch32_instrs_TSB_Op_A_txt (_ : Unit) : Unit :=
  (TraceSynchronizationBarrier ())


def execute_aarch32_instrs_CSDB_Op_A_txt (_ : Unit) : SailM Unit := do
  (ConsumptionOfSpeculativeDataBarrier ())


def execute_aarch32_instrs_SSBB_Op_A_txt (_ : Unit) : SailM Unit := do
  (SpeculativeStoreBypassBarrierToVA ())


def execute_aarch32_instrs_PSSBB_Op_A_txt (_ : Unit) : Unit :=
  (SpeculativeStoreBypassBarrierToPA ())


def execute_aarch32_instrs_CLRBHB_Op_A_txt (_ : Unit) : Unit :=
  (Hint_CLRBHB ())


def execute_aarch64_instrs_system_monitors (_ : Unit) : Unit :=
  (ClearExclusiveLocal (ProcessorID ()))


def execute_aarch64_instrs_system_barriers_dmb (domain : MBReqDomain) (types : MBReqTypes) : SailM Unit := do
  (DataMemoryBarrier domain types)


def execute_aarch64_instrs_system_barriers_sb (_ : Unit) : SailM Unit := do
  (SpeculationBarrier ())


/-- Type quantifiers: pc : Int -/
def __DecodeA64_Reserved (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  let w__1 ← (( do
    if ((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb __opcode 31 16)) == (0x0000#16 : (BitVec 16))) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__0 <b 1017) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      writeReg SEE 1017
      let imm16 := (BitVec.slice __opcode 0 16)
      (decode_udf_perm_undef_aarch64_instrs_udf imm16))
  else sailThrow ((Error_Undefined ()))


def __DefaultCond (enc : __InstrEnc) : SailM (BitVec 4) := do
  let cond ← (( do (undefined_bitvector_at (← occLabel 7631) 4) ) : SailM (BitVec 4) )
  let w__1 ← (( do
    if ((((BEq.beq enc __A64) || (BEq.beq enc __A32)) : Bool) : Bool)
    then (pure true)
    else
      (do
        let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure ((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb w__0.IT 3 0)) == (Sail.BitVec.castWidth (m := 4) (Zeros
              (n := 4)))) : Bool)))) ) : SailM Bool )
  if (w__1 : Bool)
  then (pure (0xE#4))
  else
    (do
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      let cond := ((Sail.BitVec.extractLsb w__2.IT 7 4) : (BitVec 4))
      (pure (cond)))


def initialize_registers_0 (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (undefined_int_at (.site 7641) ()) ) : SailM Int )
  writeReg SEE w__0
  let w__1 ← (( do (undefined_bool_at (.site 7642) ()) ) : SailM Bool )
  let w__2 ← (( do (undefined_vector 259 w__1) ) : SailM (Vector Bool 259) )
  writeReg FeatureImpl w__2
  let w__3 ← (( do (undefined_bool_at (.site 7643) ()) ) : SailM Bool )
  let w__4 ← (( do (undefined_vector 16 w__3) ) : SailM (Vector Bool 16) )
  writeReg VariantImplemented w__4
  let w__5 ← (( do (undefined_bitvector_at (.site 7644) 32) ) : SailM (BitVec 32) )
  writeReg __trcclaim_tags w__5
  let w__6 ← (( do (undefined_int_at (.site 7645) ()) ) : SailM Int )
  writeReg __cycle_count w__6
  let w__7 ← (( do (undefined_Signal (.site 7646) ()) ) : SailM Signal )
  writeReg CP15SDISABLE w__7
  let w__8 ← (( do (undefined_Signal (.site 7647) ()) ) : SailM Signal )
  writeReg CP15SDISABLE2 w__8
  let w__9 ← (( do (undefined_bool_at (.site 7648) ()) ) : SailM Bool )
  writeReg IsWFIsleep w__9
  let w__10 ← (( do (undefined_bool_at (.site 7649) ()) ) : SailM Bool )
  writeReg IsWFEsleep w__10
  let w__11 ← (( do (undefined_Configuration_Type (.site 7650) ()) ) : SailM (BitVec 32) )
  writeReg _ConfigReg w__11
  let w__12 ← (( do (undefined_DormantCtl_Type (.site 7651) ()) ) : SailM (BitVec 32) )
  writeReg _DormantCtlReg w__12
  let w__13 ← (( do (undefined_int_at (.site 7652) ()) ) : SailM Int )
  let w__14 ← (( do (undefined_vector 31 w__13) ) : SailM (Vector Int 31) )
  writeReg PMUEventAccumulator w__14
  let w__15 ← (( do (undefined_bool_at (.site 7653) ()) ) : SailM Bool )
  let w__16 ← (( do (undefined_vector 31 w__15) ) : SailM (Vector Bool 31) )
  writeReg PMULastThresholdValue w__16
  let w__17 ← (( do (undefined_int_at (.site 7654) ()) ) : SailM Int )
  writeReg __clock_divider w__17
  let w__18 ← (( do (undefined_ProcState (.site 7655) ()) ) : SailM ProcState )
  writeReg PSTATE w__18
  let w__19 ← (( do (undefined_bool_at (.site 7656) ()) ) : SailM Bool )
  writeReg ShouldAdvanceIT w__19
  let w__20 ← (( do (undefined_bool_at (.site 7657) ()) ) : SailM Bool )
  writeReg ShouldAdvanceSS w__20
  let w__21 ← (( do (undefined_bitvector_at (.site 7658) 1) ) : SailM (BitVec 1) )
  writeReg EventRegister w__21
  let w__22 ← (( do (undefined_bitvector_at (.site 7659) 64) ) : SailM (BitVec 64) )
  writeReg R0 w__22
  let w__23 ← (( do (undefined_bitvector_at (.site 7660) 64) ) : SailM (BitVec 64) )
  writeReg R1 w__23
  let w__24 ← (( do (undefined_bitvector_at (.site 7661) 64) ) : SailM (BitVec 64) )
  writeReg R2 w__24
  let w__25 ← (( do (undefined_bitvector_at (.site 7662) 64) ) : SailM (BitVec 64) )
  writeReg R3 w__25
  let w__26 ← (( do (undefined_bitvector_at (.site 7663) 64) ) : SailM (BitVec 64) )
  writeReg R4 w__26
  let w__27 ← (( do (undefined_bitvector_at (.site 7664) 64) ) : SailM (BitVec 64) )
  writeReg R5 w__27
  let w__28 ← (( do (undefined_bitvector_at (.site 7665) 64) ) : SailM (BitVec 64) )
  writeReg R6 w__28
  let w__29 ← (( do (undefined_bitvector_at (.site 7666) 64) ) : SailM (BitVec 64) )
  writeReg R7 w__29
  let w__30 ← (( do (undefined_bitvector_at (.site 7667) 64) ) : SailM (BitVec 64) )
  writeReg R8 w__30
  let w__31 ← (( do (undefined_bitvector_at (.site 7668) 64) ) : SailM (BitVec 64) )
  writeReg R9 w__31
  let w__32 ← (( do (undefined_bitvector_at (.site 7669) 64) ) : SailM (BitVec 64) )
  writeReg R10 w__32
  let w__33 ← (( do (undefined_bitvector_at (.site 7670) 64) ) : SailM (BitVec 64) )
  writeReg R11 w__33
  let w__34 ← (( do (undefined_bitvector_at (.site 7671) 64) ) : SailM (BitVec 64) )
  writeReg R12 w__34
  let w__35 ← (( do (undefined_bitvector_at (.site 7672) 64) ) : SailM (BitVec 64) )
  writeReg R13 w__35
  let w__36 ← (( do (undefined_bitvector_at (.site 7673) 64) ) : SailM (BitVec 64) )
  writeReg R14 w__36
  let w__37 ← (( do (undefined_bitvector_at (.site 7674) 64) ) : SailM (BitVec 64) )
  writeReg R15 w__37
  let w__38 ← (( do (undefined_bitvector_at (.site 7675) 64) ) : SailM (BitVec 64) )
  writeReg R16 w__38
  let w__39 ← (( do (undefined_bitvector_at (.site 7676) 64) ) : SailM (BitVec 64) )
  writeReg R17 w__39
  let w__40 ← (( do (undefined_bitvector_at (.site 7677) 64) ) : SailM (BitVec 64) )
  writeReg R18 w__40
  let w__41 ← (( do (undefined_bitvector_at (.site 7678) 64) ) : SailM (BitVec 64) )
  writeReg R19 w__41
  let w__42 ← (( do (undefined_bitvector_at (.site 7679) 64) ) : SailM (BitVec 64) )
  writeReg R20 w__42
  let w__43 ← (( do (undefined_bitvector_at (.site 7680) 64) ) : SailM (BitVec 64) )
  writeReg R21 w__43
  let w__44 ← (( do (undefined_bitvector_at (.site 7681) 64) ) : SailM (BitVec 64) )
  writeReg R22 w__44
  let w__45 ← (( do (undefined_bitvector_at (.site 7682) 64) ) : SailM (BitVec 64) )
  writeReg R23 w__45
  let w__46 ← (( do (undefined_bitvector_at (.site 7683) 64) ) : SailM (BitVec 64) )
  writeReg R24 w__46
  let w__47 ← (( do (undefined_bitvector_at (.site 7684) 64) ) : SailM (BitVec 64) )
  writeReg R25 w__47
  let w__48 ← (( do (undefined_bitvector_at (.site 7685) 64) ) : SailM (BitVec 64) )
  writeReg R26 w__48
  let w__49 ← (( do (undefined_bitvector_at (.site 7686) 64) ) : SailM (BitVec 64) )
  writeReg R27 w__49
  let w__50 ← (( do (undefined_bitvector_at (.site 7687) 64) ) : SailM (BitVec 64) )
  writeReg R28 w__50
  let w__51 ← (( do (undefined_bitvector_at (.site 7688) 64) ) : SailM (BitVec 64) )
  writeReg R29 w__51

def initialize_registers_1 (_ : Unit) : SailM Unit := do
  let w__52 ← (( do (undefined_bitvector_at (.site 7689) 64) ) : SailM (BitVec 64) )
  writeReg R30 w__52
  let w__53 ← (( do (undefined_bitvector_at (.site 7690) 64) ) : SailM (BitVec 64) )
  writeReg _PC w__53
  let w__54 ← (( do (undefined_bitvector_at (.site 7691) 88) ) : SailM (BitVec 88) )
  writeReg PhysicalCount w__54
  let w__55 ← (( do (undefined_bitvector_at (.site 7692) 64) ) : SailM (BitVec 64) )
  let w__56 ← (( do (undefined_vector 5 w__55) ) : SailM (Vector (BitVec 64) 5) )
  writeReg RC w__56
  let w__57 ← (( do (undefined_bool_at (.site 7693) ()) ) : SailM Bool )
  writeReg InGuardedPage w__57
  let w__58 ← (( do (undefined_bitvector_at (.site 7694) 2) ) : SailM (BitVec 2) )
  writeReg BTypeNext w__58
  let w__59 ← (( do (undefined_bool_at (.site 7695) ()) ) : SailM Bool )
  writeReg BTypeCompatible w__59
  let w__60 ← (( do (undefined_bitvector_at (.site 7696) 2048) ) : SailM (BitVec 2048) )
  let w__61 ← (( do (undefined_vector 32 w__60) ) : SailM (Vector (BitVec 2048) 32) )
  writeReg _Z w__61
  let w__62 ← (( do (undefined_bitvector_at (.site 7697) 256) ) : SailM (BitVec 256) )
  let w__63 ← (( do (undefined_vector 16 w__62) ) : SailM (Vector (BitVec 256) 16) )
  writeReg _P w__63
  let w__64 ← (( do (undefined_bitvector_at (.site 7698) 256) ) : SailM (BitVec 256) )
  writeReg _FFR w__64
  let w__65 ← (( do (undefined_bitvector_at (.site 7699) 2048) ) : SailM (BitVec 2048) )
  let w__66 ← (( do (undefined_vector 256 w__65) ) : SailM (Vector (BitVec 2048) 256) )
  writeReg _ZA w__66
  let w__67 ← (( do (undefined_bitvector_at (.site 7700) 512) ) : SailM (BitVec 512) )
  writeReg _ZT0 w__67
  let w__68 ← (( do (undefined_FPCR_Type (.site 7701) ()) ) : SailM (BitVec 64) )
  writeReg FPCR w__68
  let w__69 ← (( do (undefined_FPSR_Type (.site 7702) ()) ) : SailM (BitVec 64) )
  writeReg FPSR w__69
  let w__70 ← (( do (undefined_ICC_PMR_EL1_Type (.site 7703) ()) ) : SailM (BitVec 64) )
  writeReg ICC_PMR_EL1 w__70
  let w__71 ← (( do (undefined_TMState (.site 7704) ()) ) : SailM TMState )
  writeReg TSTATE w__71
  let w__72 ← (( do (undefined_bool_at (.site 7705) ()) ) : SailM Bool )
  writeReg SPESampleInFlight w__72
  let w__73 ← (( do (undefined_bitvector_at (.site 7706) 32) ) : SailM (BitVec 32) )
  writeReg SPESampleContextEL1 w__73
  let w__74 ← (( do (undefined_bool_at (.site 7707) ()) ) : SailM Bool )
  writeReg SPESampleContextEL1Valid w__74
  let w__75 ← (( do (undefined_bitvector_at (.site 7708) 32) ) : SailM (BitVec 32) )
  writeReg SPESampleContextEL2 w__75
  let w__76 ← (( do (undefined_bool_at (.site 7709) ()) ) : SailM Bool )
  writeReg SPESampleContextEL2Valid w__76
  let w__77 ← (( do (undefined_bool_at (.site 7710) ()) ) : SailM Bool )
  writeReg SPESampleInstIsNV2 w__77
  let w__78 ← (( do (undefined_bitvector_at (.site 7711) 64) ) : SailM (BitVec 64) )
  writeReg SPESamplePreviousBranchAddress w__78
  let w__79 ← (( do (undefined_bool_at (.site 7712) ()) ) : SailM Bool )
  writeReg SPESamplePreviousBranchAddressValid w__79
  let w__80 ← (( do (undefined_bitvector_at (.site 7713) 16) ) : SailM (BitVec 16) )
  writeReg SPESampleDataSource w__80
  let w__81 ← (( do (undefined_bool_at (.site 7714) ()) ) : SailM Bool )
  writeReg SPESampleDataSourceValid w__81
  let w__82 ← (( do (undefined_OpType (.site 7715) ()) ) : SailM OpType )
  writeReg SPESampleOpType w__82
  let w__83 ← (( do (undefined_bitvector_at (.site 7716) 2) ) : SailM (BitVec 2) )
  writeReg SPESampleClass w__83
  let w__84 ← (( do (undefined_bitvector_at (.site 7717) 8) ) : SailM (BitVec 8) )
  writeReg SPESampleSubclass w__84
  let w__85 ← (( do (undefined_bool_at (.site 7718) ()) ) : SailM Bool )
  writeReg SPESampleSubclassValid w__85
  let w__86 ← (( do (undefined_bitvector_at (.site 7719) 64) ) : SailM (BitVec 64) )
  writeReg SPESampleTimestamp w__86
  let w__87 ← (( do (undefined_bool_at (.site 7720) ()) ) : SailM Bool )
  writeReg SPESampleTimestampValid w__87
  let w__88 ← (( do (undefined_bitvector_at (.site 7721) 64) ) : SailM (BitVec 64) )
  writeReg SPESampleEvents w__88
  let w__89 ← (( do (undefined_bitvector_at (.site 7722) 24) ) : SailM (BitVec 24) )
  writeReg __SPE_LFSR w__89
  let w__90 ← (( do (undefined_bool_at (.site 7723) ()) ) : SailM Bool )
  writeReg __SPE_LFSR_initialized w__90
  let w__91 ← (( do (undefined_int_at (.site 7724) ()) ) : SailM Int )
  writeReg SPERecordSize w__91
  let w__92 ← (( do (undefined_int_at (.site 7725) ()) ) : SailM Int )
  writeReg __last_cycle_count w__92
  let w__93 ← (( do (undefined_bool_at (.site 7726) ()) ) : SailM Bool )
  writeReg __last_branch_valid w__93
  let w__94 ← (( do (undefined_Signal (.site 7727) ()) ) : SailM Signal )
  writeReg DBGEN w__94
  let w__95 ← (( do (undefined_Signal (.site 7728) ()) ) : SailM Signal )
  writeReg NIDEN w__95
  let w__96 ← (( do (undefined_Signal (.site 7729) ()) ) : SailM Signal )
  writeReg SPIDEN w__96
  let w__97 ← (( do (undefined_Signal (.site 7730) ()) ) : SailM Signal )
  writeReg SPNIDEN w__97
  let w__98 ← (( do (undefined_Signal (.site 7731) ()) ) : SailM Signal )
  writeReg RLPIDEN w__98
  let w__99 ← (( do (undefined_Signal (.site 7732) ()) ) : SailM Signal )
  writeReg RTPIDEN w__99
  let w__100 ← (( do (undefined_bool_at (.site 7733) ()) ) : SailM Bool )
  writeReg __InstructionStep w__100
  let w__101 ← (( do (undefined_bitvector_at (.site 7734) 56) ) : SailM (BitVec 56) )
  writeReg __CNTReadBase w__101
  let w__102 ← (( do (undefined_bitvector_at (.site 7735) 56) ) : SailM (BitVec 56) )
  writeReg __CNTBaseN w__102
  let w__103 ← (( do (undefined_bitvector_at (.site 7736) 56) ) : SailM (BitVec 56) )
  writeReg __CNTEL0BaseN w__103

def initialize_registers_2 (_ : Unit) : SailM Unit := do
  let w__104 ← (( do (undefined_bitvector_at (.site 7737) 56) ) : SailM (BitVec 56) )
  writeReg __CNTCTLBase w__104
  let w__105 ← (( do (undefined_bitvector_at (.site 7738) 56) ) : SailM (BitVec 56) )
  writeReg __RD_base w__105
  let w__106 ← (( do (undefined_bitvector_at (.site 7739) 56) ) : SailM (BitVec 56) )
  writeReg __SGI_base w__106
  let w__107 ← (( do (undefined_bitvector_at (.site 7740) 56) ) : SailM (BitVec 56) )
  writeReg __VLPI_base w__107
  let w__108 ← (( do (undefined_bitvector_at (.site 7741) 56) ) : SailM (BitVec 56) )
  writeReg __ETEBase w__108
  let w__109 ← (( do (undefined_bitvector_at (.site 7742) 32) ) : SailM (BitVec 32) )
  writeReg __ThisInstr w__109
  let w__110 ← (( do (undefined___InstrEnc (.site 7743) ()) ) : SailM __InstrEnc )
  writeReg __ThisInstrEnc w__110
  let w__111 ← (( do (undefined_bitvector_at (.site 7744) 4) ) : SailM (BitVec 4) )
  writeReg __currentCond w__111
  let w__112 ← (( do (undefined_BranchType (.site 7745) ()) ) : SailM BranchType )
  writeReg Branchtypetaken w__112
  let w__113 ← (( do (undefined_bool_at (.site 7746) ()) ) : SailM Bool )
  writeReg __BranchTaken w__113
  let w__114 ← (( do (undefined_bool_at (.site 7747) ()) ) : SailM Bool )
  writeReg __ExclusiveMonitorSet w__114
  let w__115 ← (( do (undefined_bool_at (.site 7748) ()) ) : SailM Bool )
  writeReg __highest_el_aarch32 w__115
  let w__116 ← (( do (undefined_bitvector_at (.site 7749) 64) ) : SailM (BitVec 64) )
  let w__117 ← (( do (undefined_vector 7 w__116) ) : SailM (Vector (BitVec 64) 7) )
  writeReg __ICACHE_CCSIDR_RESET w__117
  let w__118 ← (( do (undefined_bitvector_at (.site 7750) 64) ) : SailM (BitVec 64) )
  let w__119 ← (( do (undefined_vector 7 w__118) ) : SailM (Vector (BitVec 64) 7) )
  writeReg __DCACHE_CCSIDR_RESET w__119
  let w__120 ← (( do (undefined_bitvector_at (.site 7751) 64) ) : SailM (BitVec 64) )
  writeReg sp_rel_access_pc w__120
  let w__121 ← (( do (undefined_bitvector_at (.site 7752) 32) ) : SailM (BitVec 32) )
  writeReg SP_mon w__121
  let w__122 ← (( do (undefined_bitvector_at (.site 7753) 32) ) : SailM (BitVec 32) )
  writeReg LR_mon w__122
  let w__123 ← (( do (undefined_bitvector_at (.site 7754) 64) ) : SailM (BitVec 64) )
  let w__124 ← (( do (undefined_vector 32 w__123) ) : SailM (Vector (BitVec 64) 32) )
  writeReg _Dclone w__124
  let w__125 ← (( do (undefined_HCR_EL2_Type (.site 7755) ()) ) : SailM (BitVec 64) )
  writeReg HCR_EL2 w__125
  let w__126 ← (( do (undefined_SCR_EL3_Type (.site 7756) ()) ) : SailM (BitVec 64) )
  writeReg SCR_EL3 w__126
  let w__127 ← (( do (undefined_SCR_Type (.site 7757) ()) ) : SailM (BitVec 32) )
  writeReg SCR w__127
  let w__128 ← (( do (undefined_FPSCR_Type (.site 7758) ()) ) : SailM (BitVec 32) )
  writeReg _FPSCR w__128
  let w__129 ← (( do (undefined_bitvector_at (.site 7759) 32) ) : SailM (BitVec 32) )
  writeReg RVBAR w__129
  let w__130 ← (( do (undefined_ERRnFR_ElemType (.site 7760) ()) ) : SailM (BitVec 64) )
  let w__131 ← (( do (undefined_vector 4 w__130) ) : SailM (Vector (BitVec 64) 4) )
  writeReg ERRnFR w__131
  let w__132 ← (( do (undefined_CTR_EL0_Type (.site 7761) ()) ) : SailM (BitVec 64) )
  writeReg CTR_EL0 w__132
  let w__133 ← (( do (undefined_MDCR_EL2_Type (.site 7762) ()) ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 w__133
  let w__134 ← (( do (undefined_HDCR_Type (.site 7763) ()) ) : SailM (BitVec 32) )
  writeReg _HDCR w__134
  let w__135 ← (( do (undefined_MDCCSR_EL0_Type (.site 7764) ()) ) : SailM (BitVec 64) )
  writeReg MDCCSR_EL0 w__135
  let w__136 ← (( do (undefined_EDSCR_Type (.site 7765) ()) ) : SailM (BitVec 32) )
  writeReg _EDSCR w__136
  let w__137 ← (( do (undefined_PMCNTENCLR_EL0_Type (.site 7766) ()) ) : SailM (BitVec 64) )
  writeReg PMCNTENCLR_EL0 w__137
  let w__138 ← (( do (undefined_PMCNTENCLR_Type (.site 7767) ()) ) : SailM (BitVec 32) )
  writeReg _PMCNTENCLR w__138
  let w__139 ← (( do (undefined_PMCR_EL0_Type (.site 7768) ()) ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 w__139
  let w__140 ← (( do (undefined_PMCR_Type (.site 7769) ()) ) : SailM (BitVec 32) )
  writeReg _PMCR w__140
  let w__141 ← (( do (undefined_PMINTENCLR_EL1_Type (.site 7770) ()) ) : SailM (BitVec 64) )
  writeReg PMINTENCLR_EL1 w__141
  let w__142 ← (( do (undefined_PMINTENCLR_Type (.site 7771) ()) ) : SailM (BitVec 32) )
  writeReg _PMINTENCLR w__142
  let w__143 ← (( do (undefined_PMOVSCLR_EL0_Type (.site 7772) ()) ) : SailM (BitVec 64) )
  writeReg PMOVSCLR_EL0 w__143
  let w__144 ← (( do (undefined_PMOVSR_Type (.site 7773) ()) ) : SailM (BitVec 32) )
  writeReg _PMOVSR w__144
  let w__145 ← (( do (undefined_MDCR_EL3_Type (.site 7774) ()) ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 w__145
  let w__146 ← (( do (undefined_PMCCFILTR_EL0_Type (.site 7775) ()) ) : SailM (BitVec 64) )
  writeReg PMCCFILTR_EL0 w__146
  let w__147 ← (( do (undefined_PMCCFILTR_Type (.site 7776) ()) ) : SailM (BitVec 32) )
  writeReg _PMCCFILTR w__147
  let w__148 ← (( do (undefined_PMCNTENSET_EL0_Type (.site 7777) ()) ) : SailM (BitVec 64) )
  writeReg PMCNTENSET_EL0 w__148
  let w__149 ← (( do (undefined_PMCNTENSET_Type (.site 7778) ()) ) : SailM (BitVec 32) )
  writeReg _PMCNTENSET w__149
  let w__150 ← (( do (undefined_PMEVTYPER_EL0_Type (.site 7779) ()) ) : SailM (BitVec 64) )
  let w__151 ← (( do (undefined_vector 32 w__150) ) : SailM (Vector (BitVec 64) 32) )
  writeReg PMEVTYPER_EL0 w__151
  let w__152 ← (( do (undefined_PMEVTYPER_Type (.site 7780) ()) ) : SailM (BitVec 32) )
  let w__153 ← (( do (undefined_vector 31 w__152) ) : SailM (Vector (BitVec 32) 31) )
  writeReg _PMEVTYPER w__153
  let w__154 ← (( do (undefined_PMICFILTR_EL0_Type (.site 7781) ()) ) : SailM (BitVec 64) )
  writeReg PMICFILTR_EL0 w__154
  let w__155 ← (( do (undefined_SDCR_Type (.site 7782) ()) ) : SailM (BitVec 32) )
  writeReg SDCR w__155
  let w__156 ← (( do (undefined_SDER32_EL2_Type (.site 7783) ()) ) : SailM (BitVec 64) )
  writeReg SDER32_EL2 w__156
  let w__157 ← (( do (undefined_SDER32_EL3_Type (.site 7784) ()) ) : SailM (BitVec 64) )
  writeReg _SDER32_EL3 w__157

def initialize_registers_3 (_ : Unit) : SailM Unit := do
  let w__158 ← (( do (undefined_SDER_Type (.site 7785) ()) ) : SailM (BitVec 32) )
  writeReg _SDER w__158
  let w__159 ← (( do (undefined_PMICNTR_EL0_Type (.site 7786) ()) ) : SailM (BitVec 64) )
  writeReg PMICNTR_EL0 w__159
  let w__160 ← (( do (undefined_PMOVSSET_EL0_Type (.site 7787) ()) ) : SailM (BitVec 64) )
  writeReg PMOVSSET_EL0 w__160
  let w__161 ← (( do (undefined_BRBCR_EL1_Type (.site 7788) ()) ) : SailM (BitVec 64) )
  writeReg BRBCR_EL1 w__161
  let w__162 ← (( do (undefined_BRBCR_EL2_Type (.site 7789) ()) ) : SailM (BitVec 64) )
  writeReg BRBCR_EL2 w__162
  let w__163 ← (( do (undefined_BRBFCR_EL1_Type (.site 7790) ()) ) : SailM (BitVec 64) )
  writeReg BRBFCR_EL1 w__163
  let w__164 ← (( do (undefined_BRBTS_EL1_Type (.site 7791) ()) ) : SailM (BitVec 64) )
  writeReg BRBTS_EL1 w__164
  let w__165 ← (( do (undefined_bitvector_at (.site 7792) 64) ) : SailM (BitVec 64) )
  writeReg CNTPOFF_EL2 w__165
  let w__166 ← (( do (undefined_bitvector_at (.site 7793) 64) ) : SailM (BitVec 64) )
  writeReg CNTVOFF_EL2 w__166
  let w__167 ← (( do (undefined_CNTHCTL_EL2_Type (.site 7794) ()) ) : SailM (BitVec 64) )
  writeReg CNTHCTL_EL2 w__167
  let w__168 ← (( do (undefined_EDECR_Type (.site 7795) ()) ) : SailM (BitVec 32) )
  writeReg EDECR w__168
  let w__169 ← (( do (undefined_bitvector_at (.site 7796) 64) ) : SailM (BitVec 64) )
  writeReg DLR_EL0 w__169
  let w__170 ← (( do (undefined_bitvector_at (.site 7797) 32) ) : SailM (BitVec 32) )
  writeReg _DLR w__170
  let w__171 ← (( do (undefined_DSPSR_EL0_Type (.site 7798) ()) ) : SailM (BitVec 64) )
  writeReg DSPSR_EL0 w__171
  let w__172 ← (( do (undefined_DSPSR_Type (.site 7799) ()) ) : SailM (BitVec 32) )
  writeReg _DSPSR w__172
  let w__173 ← (( do (undefined_DSPSR2_Type (.site 7800) ()) ) : SailM (BitVec 32) )
  writeReg _DSPSR2 w__173
  let w__174 ← (( do (undefined_TCR_EL1_Type (.site 7801) ()) ) : SailM (BitVec 64) )
  writeReg TCR_EL1 w__174
  let w__175 ← (( do (undefined_TCR_EL2_Type (.site 7802) ()) ) : SailM (BitVec 64) )
  writeReg TCR_EL2 w__175
  let w__176 ← (( do (undefined_TCR_EL3_Type (.site 7803) ()) ) : SailM (BitVec 64) )
  writeReg TCR_EL3 w__176
  let w__177 ← (( do (undefined_BRBIDR0_EL1_Type (.site 7804) ()) ) : SailM (BitVec 64) )
  writeReg BRBIDR0_EL1 w__177
  let w__178 ← (( do (undefined_BRBINFType (.site 7805) ()) ) : SailM (BitVec 64) )
  let w__179 ← (( do (undefined_vector 64 w__178) ) : SailM (Vector (BitVec 64) 64) )
  writeReg Records_INF w__179
  let w__180 ← (( do (undefined_BRBSRCType (.site 7806) ()) ) : SailM (BitVec 64) )
  let w__181 ← (( do (undefined_vector 64 w__180) ) : SailM (Vector (BitVec 64) 64) )
  writeReg Records_SRC w__181
  let w__182 ← (( do (undefined_BRBTGTType (.site 7807) ()) ) : SailM (BitVec 64) )
  let w__183 ← (( do (undefined_vector 64 w__182) ) : SailM (Vector (BitVec 64) 64) )
  writeReg Records_TGT w__183
  let w__184 ← (( do (undefined_PMSIDR_EL1_Type (.site 7808) ()) ) : SailM (BitVec 64) )
  writeReg PMSIDR_EL1 w__184
  let w__185 ← (( do (undefined_bitvector_at (.site 7809) 64) ) : SailM (BitVec 64) )
  let w__186 ← (( do (undefined_vector 32 w__185) ) : SailM (Vector (BitVec 64) 32) )
  writeReg SPESampleAddress w__186
  let w__187 ← (( do (undefined_bool_at (.site 7810) ()) ) : SailM Bool )
  let w__188 ← (( do (undefined_vector 32 w__187) ) : SailM (Vector Bool 32) )
  writeReg SPESampleAddressValid w__188
  let w__189 ← (( do (undefined_PMSCR_EL1_Type (.site 7811) ()) ) : SailM (BitVec 64) )
  writeReg PMSCR_EL1 w__189
  let w__190 ← (( do (undefined_PMSCR_EL2_Type (.site 7812) ()) ) : SailM (BitVec 64) )
  writeReg PMSCR_EL2 w__190
  let w__191 ← (( do (undefined_PMBLIMITR_EL1_Type (.site 7813) ()) ) : SailM (BitVec 64) )
  writeReg PMBLIMITR_EL1 w__191
  let w__192 ← (( do (undefined_PMBSR_EL1_Type (.site 7814) ()) ) : SailM (BitVec 64) )
  writeReg PMBSR_EL1 w__192
  let w__193 ← (( do (undefined_ZCR_EL1_Type (.site 7815) ()) ) : SailM (BitVec 64) )
  writeReg ZCR_EL1 w__193
  let w__194 ← (( do (undefined_ZCR_EL2_Type (.site 7816) ()) ) : SailM (BitVec 64) )
  writeReg ZCR_EL2 w__194
  let w__195 ← (( do (undefined_ZCR_EL3_Type (.site 7817) ()) ) : SailM (BitVec 64) )
  writeReg ZCR_EL3 w__195
  let w__196 ← (( do (undefined_SMCR_EL1_Type (.site 7818) ()) ) : SailM (BitVec 64) )
  writeReg SMCR_EL1 w__196
  let w__197 ← (( do (undefined_SMCR_EL2_Type (.site 7819) ()) ) : SailM (BitVec 64) )
  writeReg SMCR_EL2 w__197
  let w__198 ← (( do (undefined_SMCR_EL3_Type (.site 7820) ()) ) : SailM (BitVec 64) )
  writeReg SMCR_EL3 w__198
  let w__199 ← (( do (undefined_GCSPR_EL0_Type (.site 7821) ()) ) : SailM (BitVec 64) )
  writeReg GCSPR_EL0 w__199
  let w__200 ← (( do (undefined_GCSPR_EL1_Type (.site 7822) ()) ) : SailM (BitVec 64) )
  writeReg GCSPR_EL1 w__200
  let w__201 ← (( do (undefined_GCSPR_EL2_Type (.site 7823) ()) ) : SailM (BitVec 64) )
  writeReg GCSPR_EL2 w__201
  let w__202 ← (( do (undefined_GCSPR_EL3_Type (.site 7824) ()) ) : SailM (BitVec 64) )
  writeReg GCSPR_EL3 w__202
  let w__203 ← (( do (undefined_CPACR_EL1_Type (.site 7825) ()) ) : SailM (BitVec 64) )
  writeReg CPACR_EL1 w__203
  let w__204 ← (( do (undefined_CPTR_EL2_Type (.site 7826) ()) ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 w__204
  let w__205 ← (( do (undefined_CPTR_EL3_Type (.site 7827) ()) ) : SailM (BitVec 64) )
  writeReg CPTR_EL3 w__205
  let w__206 ← (( do (undefined_CPACR_Type (.site 7828) ()) ) : SailM (BitVec 32) )
  writeReg _CPACR w__206
  let w__207 ← (( do (undefined_HCPTR_Type (.site 7829) ()) ) : SailM (BitVec 32) )
  writeReg _HCPTR w__207
  let w__208 ← (( do (undefined_NSACR_Type (.site 7830) ()) ) : SailM (BitVec 32) )
  writeReg NSACR w__208
  let w__209 ← (( do (undefined_bitvector_at (.site 7831) 64) ) : SailM (BitVec 64) )
  writeReg SP_EL0 w__209
  let w__210 ← (( do (undefined_bitvector_at (.site 7832) 64) ) : SailM (BitVec 64) )
  writeReg SP_EL1 w__210

def initialize_registers_4 (_ : Unit) : SailM Unit := do
  let w__211 ← (( do (undefined_bitvector_at (.site 7833) 64) ) : SailM (BitVec 64) )
  writeReg SP_EL2 w__211
  let w__212 ← (( do (undefined_bitvector_at (.site 7834) 64) ) : SailM (BitVec 64) )
  writeReg SP_EL3 w__212
  let w__213 ← (( do (undefined_OSDLR_EL1_Type (.site 7835) ()) ) : SailM (BitVec 64) )
  writeReg OSDLR_EL1 w__213
  let w__214 ← (( do (undefined_DBGOSDLR_Type (.site 7836) ()) ) : SailM (BitVec 32) )
  writeReg _DBGOSDLR w__214
  let w__215 ← (( do (undefined_DBGPRCR_EL1_Type (.site 7837) ()) ) : SailM (BitVec 64) )
  writeReg DBGPRCR_EL1 w__215
  let w__216 ← (( do (undefined_DBGPRCR_Type (.site 7838) ()) ) : SailM (BitVec 32) )
  writeReg _DBGPRCR w__216
  let w__217 ← (( do (undefined_GCSCR_EL1_Type (.site 7839) ()) ) : SailM (BitVec 64) )
  writeReg GCSCR_EL1 w__217
  let w__218 ← (( do (undefined_GCSCR_EL2_Type (.site 7840) ()) ) : SailM (BitVec 64) )
  writeReg GCSCR_EL2 w__218
  let w__219 ← (( do (undefined_GCSCR_EL3_Type (.site 7841) ()) ) : SailM (BitVec 64) )
  writeReg GCSCR_EL3 w__219
  let w__220 ← (( do (undefined_MDSCR_EL1_Type (.site 7842) ()) ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 w__220
  let w__221 ← (( do (undefined_OSLSR_EL1_Type (.site 7843) ()) ) : SailM (BitVec 64) )
  writeReg OSLSR_EL1 w__221
  let w__222 ← (( do (undefined_DBGOSLSR_Type (.site 7844) ()) ) : SailM (BitVec 32) )
  writeReg _DBGOSLSR w__222
  let w__223 ← (( do (undefined_HCR_Type (.site 7845) ()) ) : SailM (BitVec 32) )
  writeReg _HCR w__223
  let w__224 ← (( do (undefined_SCTLR_EL2_Type (.site 7846) ()) ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 w__224
  let w__225 ← (( do (undefined_HSCTLR_Type (.site 7847) ()) ) : SailM (BitVec 32) )
  writeReg _HSCTLR w__225
  let w__226 ← (( do (undefined_SCTLR_EL1_Type (.site 7848) ()) ) : SailM (BitVec 64) )
  writeReg SCTLR_EL1 w__226
  let w__227 ← (( do (undefined_SCTLR_EL3_Type (.site 7849) ()) ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 w__227
  let w__228 ← (( do (undefined_SCTLR_Type (.site 7850) ()) ) : SailM (BitVec 32) )
  writeReg _SCTLR_NS w__228
  let w__229 ← (( do (undefined_SCTLR_Type (.site 7851) ()) ) : SailM (BitVec 32) )
  writeReg SCTLR_S w__229
  let w__230 ← (( do (undefined_ESR_EL1_Type (.site 7852) ()) ) : SailM (BitVec 64) )
  writeReg ESR_EL1 w__230
  let w__231 ← (( do (undefined_ESR_EL2_Type (.site 7853) ()) ) : SailM (BitVec 64) )
  writeReg ESR_EL2 w__231
  let w__232 ← (( do (undefined_ESR_EL3_Type (.site 7854) ()) ) : SailM (BitVec 64) )
  writeReg ESR_EL3 w__232
  let w__233 ← (( do (undefined_bitvector_at (.site 7855) 64) ) : SailM (BitVec 64) )
  writeReg FAR_EL1 w__233
  let w__234 ← (( do (undefined_bitvector_at (.site 7856) 64) ) : SailM (BitVec 64) )
  writeReg FAR_EL2 w__234
  let w__235 ← (( do (undefined_bitvector_at (.site 7857) 64) ) : SailM (BitVec 64) )
  writeReg FAR_EL3 w__235
  let w__236 ← (( do (undefined_HPFAR_EL2_Type (.site 7858) ()) ) : SailM (BitVec 64) )
  writeReg HPFAR_EL2 w__236
  let w__237 ← (( do (undefined_MFAR_EL3_Type (.site 7859) ()) ) : SailM (BitVec 64) )
  writeReg MFAR_EL3 w__237
  let w__238 ← (( do (undefined_PFAR_EL1_Type (.site 7860) ()) ) : SailM (BitVec 64) )
  writeReg PFAR_EL1 w__238
  let w__239 ← (( do (undefined_PFAR_EL2_Type (.site 7861) ()) ) : SailM (BitVec 64) )
  writeReg PFAR_EL2 w__239
  let w__240 ← (( do (undefined_bitvector_at (.site 7862) 64) ) : SailM (BitVec 64) )
  writeReg ELR_EL1 w__240
  let w__241 ← (( do (undefined_bitvector_at (.site 7863) 64) ) : SailM (BitVec 64) )
  writeReg ELR_EL2 w__241
  let w__242 ← (( do (undefined_bitvector_at (.site 7864) 64) ) : SailM (BitVec 64) )
  writeReg ELR_EL3 w__242
  let w__243 ← (( do (undefined_SPSR_EL1_Type (.site 7865) ()) ) : SailM (BitVec 64) )
  writeReg SPSR_EL1 w__243
  let w__244 ← (( do (undefined_SPSR_EL2_Type (.site 7866) ()) ) : SailM (BitVec 64) )
  writeReg SPSR_EL2 w__244
  let w__245 ← (( do (undefined_SPSR_EL3_Type (.site 7867) ()) ) : SailM (BitVec 64) )
  writeReg SPSR_EL3 w__245
  let w__246 ← (( do (undefined_SPSR_abt_Type (.site 7868) ()) ) : SailM (BitVec 64) )
  writeReg SPSR_abt w__246
  let w__247 ← (( do (undefined_SPSR_fiq_Type (.site 7869) ()) ) : SailM (BitVec 64) )
  writeReg SPSR_fiq w__247
  let w__248 ← (( do (undefined_SPSR_hyp_Type (.site 7870) ()) ) : SailM (BitVec 32) )
  writeReg _SPSR_hyp w__248
  let w__249 ← (( do (undefined_SPSR_irq_Type (.site 7871) ()) ) : SailM (BitVec 64) )
  writeReg SPSR_irq w__249
  let w__250 ← (( do (undefined_SPSR_mon_Type (.site 7872) ()) ) : SailM (BitVec 32) )
  writeReg SPSR_mon w__250
  let w__251 ← (( do (undefined_SPSR_svc_Type (.site 7873) ()) ) : SailM (BitVec 32) )
  writeReg _SPSR_svc w__251
  let w__252 ← (( do (undefined_SPSR_und_Type (.site 7874) ()) ) : SailM (BitVec 64) )
  writeReg SPSR_und w__252
  let w__253 ← (( do (undefined_OSECCR_EL1_Type (.site 7875) ()) ) : SailM (BitVec 64) )
  writeReg OSECCR_EL1 w__253
  let w__254 ← (( do (undefined_EDECCR_Type (.site 7876) ()) ) : SailM (BitVec 32) )
  writeReg _EDECCR w__254
  let w__255 ← (( do (undefined_EDESR_Type (.site 7877) ()) ) : SailM (BitVec 32) )
  writeReg EDESR w__255
  let w__256 ← (( do (undefined_bitvector_at (.site 7878) 64) ) : SailM (BitVec 64) )
  writeReg VBAR_EL1 w__256
  let w__257 ← (( do (undefined_bitvector_at (.site 7879) 64) ) : SailM (BitVec 64) )
  writeReg VBAR_EL2 w__257
  let w__258 ← (( do (undefined_bitvector_at (.site 7880) 64) ) : SailM (BitVec 64) )
  writeReg VBAR_EL3 w__258

def initialize_registers_5 (_ : Unit) : SailM Unit := do
  let w__259 ← (( do (undefined_bitvector_at (.site 7881) 32) ) : SailM (BitVec 32) )
  writeReg _VBAR_NS w__259
  let w__260 ← (( do (undefined_bitvector_at (.site 7882) 32) ) : SailM (BitVec 32) )
  writeReg VBAR_S w__260
  let w__261 ← (( do (undefined_GCSCRE0_EL1_Type (.site 7883) ()) ) : SailM (BitVec 64) )
  writeReg GCSCRE0_EL1 w__261
  let w__262 ← (( do (undefined_HCRX_EL2_Type (.site 7884) ()) ) : SailM (BitVec 64) )
  writeReg HCRX_EL2 w__262
  let w__263 ← (( do (undefined_MPAM2_EL2_Type (.site 7885) ()) ) : SailM (BitVec 64) )
  writeReg MPAM2_EL2 w__263
  let w__264 ← (( do (undefined_MPAM3_EL3_Type (.site 7886) ()) ) : SailM (BitVec 64) )
  writeReg _MPAM3_EL3 w__264
  let w__265 ← (( do (undefined_MPAM1_EL1_Type (.site 7887) ()) ) : SailM (BitVec 64) )
  writeReg _MPAM1_EL1 w__265
  let w__266 ← (( do (undefined_MPAMIDR_EL1_Type (.site 7888) ()) ) : SailM (BitVec 64) )
  writeReg MPAMIDR_EL1 w__266
  let w__267 ← (( do (undefined_MPAMHCR_EL2_Type (.site 7889) ()) ) : SailM (BitVec 64) )
  writeReg MPAMHCR_EL2 w__267
  let w__268 ← (( do (undefined_MPAMVPM0_EL2_Type (.site 7890) ()) ) : SailM (BitVec 64) )
  writeReg MPAMVPM0_EL2 w__268
  let w__269 ← (( do (undefined_MPAMVPMV_EL2_Type (.site 7891) ()) ) : SailM (BitVec 64) )
  writeReg MPAMVPMV_EL2 w__269
  let w__270 ← (( do (undefined_MPAMVPM1_EL2_Type (.site 7892) ()) ) : SailM (BitVec 64) )
  writeReg MPAMVPM1_EL2 w__270
  let w__271 ← (( do (undefined_MPAMVPM2_EL2_Type (.site 7893) ()) ) : SailM (BitVec 64) )
  writeReg MPAMVPM2_EL2 w__271
  let w__272 ← (( do (undefined_MPAMVPM3_EL2_Type (.site 7894) ()) ) : SailM (BitVec 64) )
  writeReg MPAMVPM3_EL2 w__272
  let w__273 ← (( do (undefined_MPAMVPM4_EL2_Type (.site 7895) ()) ) : SailM (BitVec 64) )
  writeReg MPAMVPM4_EL2 w__273
  let w__274 ← (( do (undefined_MPAMVPM5_EL2_Type (.site 7896) ()) ) : SailM (BitVec 64) )
  writeReg MPAMVPM5_EL2 w__274
  let w__275 ← (( do (undefined_MPAMVPM6_EL2_Type (.site 7897) ()) ) : SailM (BitVec 64) )
  writeReg MPAMVPM6_EL2 w__275
  let w__276 ← (( do (undefined_MPAMVPM7_EL2_Type (.site 7898) ()) ) : SailM (BitVec 64) )
  writeReg MPAMVPM7_EL2 w__276
  let w__277 ← (( do (undefined_MPAM0_EL1_Type (.site 7899) ()) ) : SailM (BitVec 64) )
  writeReg MPAM0_EL1 w__277
  let w__278 ← (( do (undefined_MPAMSM_EL1_Type (.site 7900) ()) ) : SailM (BitVec 64) )
  writeReg MPAMSM_EL1 w__278
  let w__279 ← (( do (undefined_CLIDR_EL1_Type (.site 7901) ()) ) : SailM (BitVec 64) )
  writeReg CLIDR_EL1 w__279
  let w__280 ← (( do (undefined_CONTEXTIDR_EL1_Type (.site 7902) ()) ) : SailM (BitVec 64) )
  writeReg CONTEXTIDR_EL1 w__280
  let w__281 ← (( do (undefined_TTBCR_Type (.site 7903) ()) ) : SailM (BitVec 32) )
  writeReg _TTBCR_NS w__281
  let w__282 ← (( do (undefined_TTBCR_Type (.site 7904) ()) ) : SailM (BitVec 32) )
  writeReg TTBCR_S w__282
  let w__283 ← (( do (undefined_CONTEXTIDR_Type (.site 7905) ()) ) : SailM (BitVec 32) )
  writeReg _CONTEXTIDR_NS w__283
  let w__284 ← (( do (undefined_CONTEXTIDR_Type (.site 7906) ()) ) : SailM (BitVec 32) )
  writeReg CONTEXTIDR_S w__284
  let w__285 ← (( do (undefined_TTBR0_Type (.site 7907) ()) ) : SailM (BitVec 64) )
  writeReg TTBR0_NS w__285
  let w__286 ← (( do (undefined_TTBR0_Type (.site 7908) ()) ) : SailM (BitVec 64) )
  writeReg TTBR0_S w__286
  let w__287 ← (( do (undefined_TTBR0_EL1_Type (.site 7909) ()) ) : SailM (BitVec 128) )
  writeReg _TTBR0_EL1 w__287
  let w__288 ← (( do (undefined_HTTBR_Type (.site 7910) ()) ) : SailM (BitVec 64) )
  writeReg HTTBR w__288
  let w__289 ← (( do (undefined_TTBR0_EL2_Type (.site 7911) ()) ) : SailM (BitVec 128) )
  writeReg _TTBR0_EL2 w__289
  let w__290 ← (( do (undefined_TTBR1_Type (.site 7912) ()) ) : SailM (BitVec 64) )
  writeReg TTBR1_NS w__290
  let w__291 ← (( do (undefined_TTBR1_Type (.site 7913) ()) ) : SailM (BitVec 64) )
  writeReg TTBR1_S w__291
  let w__292 ← (( do (undefined_TTBR1_EL1_Type (.site 7914) ()) ) : SailM (BitVec 128) )
  writeReg _TTBR1_EL1 w__292
  let w__293 ← (( do (undefined_TTBR1_EL2_Type (.site 7915) ()) ) : SailM (BitVec 128) )
  writeReg TTBR1_EL2 w__293
  let w__294 ← (( do (undefined_bitvector_at (.site 7916) 32) ) : SailM (BitVec 32) )
  writeReg _HDFAR w__294
  let w__295 ← (( do (undefined_bitvector_at (.site 7917) 32) ) : SailM (BitVec 32) )
  writeReg _HIFAR w__295
  let w__296 ← (( do (undefined_HPFAR_Type (.site 7918) ()) ) : SailM (BitVec 32) )
  writeReg _HPFAR w__296
  let w__297 ← (( do (undefined_HSR_Type (.site 7919) ()) ) : SailM (BitVec 32) )
  writeReg _HSR w__297
  let w__298 ← (( do (undefined_bitvector_at (.site 7920) 32) ) : SailM (BitVec 32) )
  writeReg _ELR_hyp w__298
  let w__299 ← (( do (undefined_bitvector_at (.site 7921) 32) ) : SailM (BitVec 32) )
  writeReg _HVBAR w__299
  let w__300 ← (( do (undefined_MVBAR_Type (.site 7922) ()) ) : SailM (BitVec 32) )
  writeReg MVBAR w__300
  let w__301 ← (( do (undefined_bitvector_at (.site 7923) 32) ) : SailM (BitVec 32) )
  writeReg _DFAR_NS w__301
  let w__302 ← (( do (undefined_bitvector_at (.site 7924) 32) ) : SailM (BitVec 32) )
  writeReg _DFAR_S w__302
  let w__303 ← (( do (undefined_DFSR_Type (.site 7925) ()) ) : SailM (BitVec 32) )
  writeReg _DFSR_NS w__303
  let w__304 ← (( do (undefined_DFSR_Type (.site 7926) ()) ) : SailM (BitVec 32) )
  writeReg DFSR_S w__304
  let w__305 ← (( do (undefined_IFSR32_EL2_Type (.site 7927) ()) ) : SailM (BitVec 64) )
  writeReg IFSR32_EL2 w__305
  let w__306 ← (( do (undefined_IFSR_Type (.site 7928) ()) ) : SailM (BitVec 32) )
  writeReg _IFSR_NS w__306

def initialize_registers_6 (_ : Unit) : SailM Unit := do
  let w__307 ← (( do (undefined_IFSR_Type (.site 7929) ()) ) : SailM (BitVec 32) )
  writeReg IFSR_S w__307
  let w__308 ← (( do (undefined_DBGDSCRint_Type (.site 7930) ()) ) : SailM (BitVec 32) )
  writeReg _DBGDSCRint w__308
  let w__309 ← (( do (undefined_DBGDSCRext_Type (.site 7931) ()) ) : SailM (BitVec 32) )
  writeReg _DBGDSCRext w__309
  let w__310 ← (( do (undefined_HCR2_Type (.site 7932) ()) ) : SailM (BitVec 32) )
  writeReg _HCR2 w__310
  let w__311 ← (( do (undefined_bitvector_at (.site 7933) 32) ) : SailM (BitVec 32) )
  writeReg _IFAR_NS w__311
  let w__312 ← (( do (undefined_bitvector_at (.site 7934) 32) ) : SailM (BitVec 32) )
  writeReg _IFAR_S w__312
  let w__313 ← (( do (undefined_SCTLR2_EL1_Type (.site 7935) ()) ) : SailM (BitVec 64) )
  writeReg SCTLR2_EL1 w__313
  let w__314 ← (( do (undefined_SCTLR2_EL2_Type (.site 7936) ()) ) : SailM (BitVec 64) )
  writeReg SCTLR2_EL2 w__314
  let w__315 ← (( do (undefined_FPEXC32_EL2_Type (.site 7937) ()) ) : SailM (BitVec 64) )
  writeReg FPEXC32_EL2 w__315
  let w__316 ← (( do (undefined_FPEXC_Type (.site 7938) ()) ) : SailM (BitVec 32) )
  writeReg _FPEXC w__316
  let w__317 ← (( do (undefined_CNTHP_CTL_EL2_Type (.site 7939) ()) ) : SailM (BitVec 64) )
  writeReg CNTHP_CTL_EL2 w__317
  let w__318 ← (( do (undefined_CNTHP_CTL_Type (.site 7940) ()) ) : SailM (BitVec 32) )
  writeReg _CNTHP_CTL w__318
  let w__319 ← (( do (undefined_CNTHP_CVAL_EL2_Type (.site 7941) ()) ) : SailM (BitVec 64) )
  writeReg CNTHP_CVAL_EL2 w__319
  let w__320 ← (( do (undefined_CNTHP_CVAL_Type (.site 7942) ()) ) : SailM (BitVec 64) )
  writeReg _CNTHP_CVAL w__320
  let w__321 ← (( do (undefined_CNTP_CTL_EL0_Type (.site 7943) ()) ) : SailM (BitVec 64) )
  writeReg CNTP_CTL_EL0 w__321
  let w__322 ← (( do (undefined_CNTP_CTL_Type (.site 7944) ()) ) : SailM (BitVec 32) )
  writeReg _CNTP_CTL_NS w__322
  let w__323 ← (( do (undefined_CNTP_CTL_Type (.site 7945) ()) ) : SailM (BitVec 32) )
  writeReg CNTP_CTL_S w__323
  let w__324 ← (( do (undefined_CNTP_CVAL_EL0_Type (.site 7946) ()) ) : SailM (BitVec 64) )
  writeReg CNTP_CVAL_EL0 w__324
  let w__325 ← (( do (undefined_CNTP_CVAL_Type (.site 7947) ()) ) : SailM (BitVec 64) )
  writeReg _CNTP_CVAL_NS w__325
  let w__326 ← (( do (undefined_CNTP_CVAL_Type (.site 7948) ()) ) : SailM (BitVec 64) )
  writeReg CNTP_CVAL_S w__326
  let w__327 ← (( do (undefined_CNTV_CTL_EL0_Type (.site 7949) ()) ) : SailM (BitVec 64) )
  writeReg CNTV_CTL_EL0 w__327
  let w__328 ← (( do (undefined_CNTV_CVAL_EL0_Type (.site 7950) ()) ) : SailM (BitVec 64) )
  writeReg CNTV_CVAL_EL0 w__328
  let w__329 ← (( do (undefined_CNTHPS_CTL_EL2_Type (.site 7951) ()) ) : SailM (BitVec 64) )
  writeReg CNTHPS_CTL_EL2 w__329
  let w__330 ← (( do (undefined_CNTHPS_CVAL_EL2_Type (.site 7952) ()) ) : SailM (BitVec 64) )
  writeReg CNTHPS_CVAL_EL2 w__330
  let w__331 ← (( do (undefined_CNTHVS_CTL_EL2_Type (.site 7953) ()) ) : SailM (BitVec 64) )
  writeReg CNTHVS_CTL_EL2 w__331
  let w__332 ← (( do (undefined_CNTHVS_CVAL_EL2_Type (.site 7954) ()) ) : SailM (BitVec 64) )
  writeReg CNTHVS_CVAL_EL2 w__332
  let w__333 ← (( do (undefined_CNTHV_CTL_EL2_Type (.site 7955) ()) ) : SailM (BitVec 64) )
  writeReg CNTHV_CTL_EL2 w__333
  let w__334 ← (( do (undefined_CNTHV_CVAL_EL2_Type (.site 7956) ()) ) : SailM (BitVec 64) )
  writeReg CNTHV_CVAL_EL2 w__334
  let w__335 ← (( do (undefined_CNTPS_CTL_EL1_Type (.site 7957) ()) ) : SailM (BitVec 64) )
  writeReg CNTPS_CTL_EL1 w__335
  let w__336 ← (( do (undefined_CNTPS_CVAL_EL1_Type (.site 7958) ()) ) : SailM (BitVec 64) )
  writeReg CNTPS_CVAL_EL1 w__336
  let w__337 ← (( do (undefined_CNTCR_Type (.site 7959) ()) ) : SailM (BitVec 32) )
  writeReg CNTCR w__337
  let w__338 ← (( do (undefined_CNTSCR_Type (.site 7960) ()) ) : SailM (BitVec 32) )
  writeReg CNTSCR w__338
  let w__339 ← (( do (undefined_CNTKCTL_EL1_Type (.site 7961) ()) ) : SailM (BitVec 64) )
  writeReg CNTKCTL_EL1 w__339
  let w__340 ← (( do (undefined_GPCCR_EL3_Type (.site 7962) ()) ) : SailM (BitVec 64) )
  writeReg GPCCR_EL3 w__340
  let w__341 ← (( do (undefined_GPTBR_EL3_Type (.site 7963) ()) ) : SailM (BitVec 64) )
  writeReg GPTBR_EL3 w__341
  let w__342 ← (( do (undefined_MAIR2_EL1_Type (.site 7964) ()) ) : SailM (BitVec 64) )
  writeReg MAIR2_EL1 w__342
  let w__343 ← (( do (undefined_MAIR_EL1_Type (.site 7965) ()) ) : SailM (BitVec 64) )
  writeReg MAIR_EL1 w__343
  let w__344 ← (( do (undefined_PIRE0_EL1_Type (.site 7966) ()) ) : SailM (BitVec 64) )
  writeReg PIRE0_EL1 w__344
  let w__345 ← (( do (undefined_PIR_EL1_Type (.site 7967) ()) ) : SailM (BitVec 64) )
  writeReg PIR_EL1 w__345
  let w__346 ← (( do (undefined_TCR2_EL1_Type (.site 7968) ()) ) : SailM (BitVec 64) )
  writeReg TCR2_EL1 w__346
  let w__347 ← (( do (undefined_MAIR2_EL2_Type (.site 7969) ()) ) : SailM (BitVec 64) )
  writeReg MAIR2_EL2 w__347
  let w__348 ← (( do (undefined_MAIR_EL2_Type (.site 7970) ()) ) : SailM (BitVec 64) )
  writeReg MAIR_EL2 w__348
  let w__349 ← (( do (undefined_PIR_EL2_Type (.site 7971) ()) ) : SailM (BitVec 64) )
  writeReg PIR_EL2 w__349
  let w__350 ← (( do (undefined_TCR2_EL2_Type (.site 7972) ()) ) : SailM (BitVec 64) )
  writeReg TCR2_EL2 w__350
  let w__351 ← (( do (undefined_PIRE0_EL2_Type (.site 7973) ()) ) : SailM (BitVec 64) )
  writeReg PIRE0_EL2 w__351
  let w__352 ← (( do (undefined_MAIR2_EL3_Type (.site 7974) ()) ) : SailM (BitVec 64) )
  writeReg MAIR2_EL3 w__352
  let w__353 ← (( do (undefined_MAIR_EL3_Type (.site 7975) ()) ) : SailM (BitVec 64) )
  writeReg MAIR_EL3 w__353
  let w__354 ← (( do (undefined_PIR_EL3_Type (.site 7976) ()) ) : SailM (BitVec 64) )
  writeReg PIR_EL3 w__354

def initialize_registers_7 (_ : Unit) : SailM Unit := do
  let w__355 ← (( do (undefined_SCTLR2_EL3_Type (.site 7977) ()) ) : SailM (BitVec 64) )
  writeReg SCTLR2_EL3 w__355
  let w__356 ← (( do (undefined_TTBR0_EL3_Type (.site 7978) ()) ) : SailM (BitVec 64) )
  writeReg TTBR0_EL3 w__356
  let w__357 ← (( do (undefined_bitvector_at (.site 7979) 64) ) : SailM (BitVec 64) )
  writeReg APIAKeyHi_EL1 w__357
  let w__358 ← (( do (undefined_bitvector_at (.site 7980) 64) ) : SailM (BitVec 64) )
  writeReg APIAKeyLo_EL1 w__358
  let w__359 ← (( do (undefined_bitvector_at (.site 7981) 64) ) : SailM (BitVec 64) )
  writeReg APIBKeyHi_EL1 w__359
  let w__360 ← (( do (undefined_bitvector_at (.site 7982) 64) ) : SailM (BitVec 64) )
  writeReg APIBKeyLo_EL1 w__360
  let w__361 ← (( do (undefined_bitvector_at (.site 7983) 64) ) : SailM (BitVec 64) )
  writeReg APDAKeyHi_EL1 w__361
  let w__362 ← (( do (undefined_bitvector_at (.site 7984) 64) ) : SailM (BitVec 64) )
  writeReg APDAKeyLo_EL1 w__362
  let w__363 ← (( do (undefined_bitvector_at (.site 7985) 64) ) : SailM (BitVec 64) )
  writeReg APDBKeyHi_EL1 w__363
  let w__364 ← (( do (undefined_bitvector_at (.site 7986) 64) ) : SailM (BitVec 64) )
  writeReg APDBKeyLo_EL1 w__364
  let w__365 ← (( do (undefined_bitvector_at (.site 7987) 64) ) : SailM (BitVec 64) )
  writeReg APGAKeyHi_EL1 w__365
  let w__366 ← (( do (undefined_bitvector_at (.site 7988) 64) ) : SailM (BitVec 64) )
  writeReg APGAKeyLo_EL1 w__366
  let w__367 ← (( do (undefined_CNTKCTL_Type (.site 7989) ()) ) : SailM (BitVec 32) )
  writeReg _CNTKCTL w__367
  let w__368 ← (( do (undefined_GCR_EL1_Type (.site 7990) ()) ) : SailM (BitVec 64) )
  writeReg GCR_EL1 w__368
  let w__369 ← (( do (undefined_RGSR_EL1_Type (.site 7991) ()) ) : SailM (BitVec 64) )
  writeReg RGSR_EL1 w__369
  let w__370 ← (( do (undefined_TFSRE0_EL1_Type (.site 7992) ()) ) : SailM (BitVec 64) )
  writeReg TFSRE0_EL1 w__370
  let w__371 ← (( do (undefined_TFSR_EL1_Type (.site 7993) ()) ) : SailM (BitVec 64) )
  writeReg TFSR_EL1 w__371
  let w__372 ← (( do (undefined_TFSR_EL2_Type (.site 7994) ()) ) : SailM (BitVec 64) )
  writeReg TFSR_EL2 w__372
  let w__373 ← (( do (undefined_TFSR_EL3_Type (.site 7995) ()) ) : SailM (BitVec 64) )
  writeReg TFSR_EL3 w__373
  let w__374 ← (( do (undefined_CONTEXTIDR_EL2_Type (.site 7996) ()) ) : SailM (BitVec 64) )
  writeReg CONTEXTIDR_EL2 w__374
  let w__375 ← (( do (undefined_DBGBCR_EL1_Type (.site 7997) ()) ) : SailM (BitVec 64) )
  let w__376 ← (( do (undefined_vector 64 w__375) ) : SailM (Vector (BitVec 64) 64) )
  writeReg DBGBCR_EL1 w__376
  let w__377 ← (( do (undefined_DBGBVR_EL1_Type (.site 7998) ()) ) : SailM (BitVec 64) )
  let w__378 ← (( do (undefined_vector 64 w__377) ) : SailM (Vector (BitVec 64) 64) )
  writeReg DBGBVR_EL1 w__378
  let w__379 ← (( do (undefined_EDSCR2_Type (.site 7999) ()) ) : SailM (BitVec 32) )
  writeReg _EDSCR2 w__379
  let w__380 ← (( do (undefined_VTCR_EL2_Type (.site 8000) ()) ) : SailM (BitVec 64) )
  writeReg VTCR_EL2 w__380
  let w__381 ← (( do (undefined_VTTBR_Type (.site 8001) ()) ) : SailM (BitVec 64) )
  writeReg VTTBR w__381
  let w__382 ← (( do (undefined_VTTBR_EL2_Type (.site 8002) ()) ) : SailM (BitVec 128) )
  writeReg _VTTBR_EL2 w__382
  let w__383 ← (( do (undefined_DBGWCR_EL1_Type (.site 8003) ()) ) : SailM (BitVec 64) )
  let w__384 ← (( do (undefined_vector 64 w__383) ) : SailM (Vector (BitVec 64) 64) )
  writeReg DBGWCR_EL1 w__384
  let w__385 ← (( do (undefined_DBGWVR_EL1_Type (.site 8004) ()) ) : SailM (BitVec 64) )
  let w__386 ← (( do (undefined_vector 64 w__385) ) : SailM (Vector (BitVec 64) 64) )
  writeReg DBGWVR_EL1 w__386
  let w__387 ← (( do (undefined_bitvector_at (.site 8005) 64) ) : SailM (BitVec 64) )
  writeReg EDWAR w__387
  let w__388 ← (( do (undefined_POR_EL1_Type (.site 8006) ()) ) : SailM (BitVec 64) )
  writeReg POR_EL1 w__388
  let w__389 ← (( do (undefined_POR_EL2_Type (.site 8007) ()) ) : SailM (BitVec 64) )
  writeReg POR_EL2 w__389
  let w__390 ← (( do (undefined_POR_EL3_Type (.site 8008) ()) ) : SailM (BitVec 64) )
  writeReg POR_EL3 w__390
  let w__391 ← (( do (undefined_POR_EL0_Type (.site 8009) ()) ) : SailM (BitVec 64) )
  writeReg POR_EL0 w__391
  let w__392 ← (( do (undefined_MECID_P0_EL2_Type (.site 8010) ()) ) : SailM (BitVec 64) )
  writeReg MECID_P0_EL2 w__392
  let w__393 ← (( do (undefined_VMECID_P_EL2_Type (.site 8011) ()) ) : SailM (BitVec 64) )
  writeReg VMECID_P_EL2 w__393
  let w__394 ← (( do (undefined_MECID_A0_EL2_Type (.site 8012) ()) ) : SailM (BitVec 64) )
  writeReg MECID_A0_EL2 w__394
  let w__395 ← (( do (undefined_MECID_A1_EL2_Type (.site 8013) ()) ) : SailM (BitVec 64) )
  writeReg MECID_A1_EL2 w__395
  let w__396 ← (( do (undefined_MECID_P1_EL2_Type (.site 8014) ()) ) : SailM (BitVec 64) )
  writeReg MECID_P1_EL2 w__396
  let w__397 ← (( do (undefined_MECID_RL_A_EL3_Type (.site 8015) ()) ) : SailM (BitVec 64) )
  writeReg MECID_RL_A_EL3 w__397
  let w__398 ← (( do (undefined_S2PIR_EL2_Type (.site 8016) ()) ) : SailM (BitVec 64) )
  writeReg S2PIR_EL2 w__398
  let w__399 ← (( do (undefined_VSTCR_EL2_Type (.site 8017) ()) ) : SailM (BitVec 64) )
  writeReg VSTCR_EL2 w__399
  let w__400 ← (( do (undefined_VSTTBR_EL2_Type (.site 8018) ()) ) : SailM (BitVec 64) )
  writeReg VSTTBR_EL2 w__400
  let w__401 ← (( do (undefined_S2POR_EL1_Type (.site 8019) ()) ) : SailM (BitVec 64) )
  writeReg S2POR_EL1 w__401
  let w__402 ← (( do (undefined_VMECID_A_EL2_Type (.site 8020) ()) ) : SailM (BitVec 64) )
  writeReg VMECID_A_EL2 w__402
  let w__403 ← (( do (undefined_bool_at (.site 8021) ()) ) : SailM Bool )
  let w__404 ← (( do (undefined_vector 32 w__403) ) : SailM (Vector Bool 32) )
  writeReg SPESampleCounterPending w__404
  let w__405 ← (( do (undefined_bool_at (.site 8022) ()) ) : SailM Bool )
  let w__406 ← (( do (undefined_vector 32 w__405) ) : SailM (Vector Bool 32) )
  writeReg SPESampleCounterValid w__406
  let w__407 ← (( do (undefined_RCWMASK_EL1_Type (.site 8023) ()) ) : SailM (BitVec 128) )
  writeReg RCWMASK_EL1 w__407
  let w__408 ← (( do (undefined_RCWSMASK_EL1_Type (.site 8024) ()) ) : SailM (BitVec 128) )
  writeReg RCWSMASK_EL1 w__408

def initialize_registers_8 (_ : Unit) : SailM Unit := do
  let w__409 ← (( do (undefined_VNCR_EL2_Type (.site 8025) ()) ) : SailM (BitVec 64) )
  writeReg VNCR_EL2 w__409
  let w__410 ← (( do (undefined_HFGITR_EL2_Type (.site 8026) ()) ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 w__410
  let w__411 ← (( do (undefined_DISR_EL1_Type (.site 8027) ()) ) : SailM (BitVec 64) )
  writeReg DISR_EL1 w__411
  let w__412 ← (( do (undefined_DISR_Type (.site 8028) ()) ) : SailM (BitVec 32) )
  writeReg _DISR w__412
  let w__413 ← (( do (undefined_VSESR_EL2_Type (.site 8029) ()) ) : SailM (BitVec 64) )
  writeReg VSESR_EL2 w__413
  let w__414 ← (( do (undefined_VDFSR_Type (.site 8030) ()) ) : SailM (BitVec 32) )
  writeReg _VDFSR w__414
  let w__415 ← (( do (undefined_VDISR_EL2_Type (.site 8031) ()) ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 w__415
  let w__416 ← (( do (undefined_VDISR_Type (.site 8032) ()) ) : SailM (BitVec 32) )
  writeReg _VDISR w__416
  let w__417 ← (( do (undefined_RVBAR_EL1_Type (.site 8033) ()) ) : SailM (BitVec 64) )
  writeReg RVBAR_EL1 w__417
  let w__418 ← (( do (undefined_RVBAR_EL2_Type (.site 8034) ()) ) : SailM (BitVec 64) )
  writeReg RVBAR_EL2 w__418
  let w__419 ← (( do (undefined_RVBAR_EL3_Type (.site 8035) ()) ) : SailM (BitVec 64) )
  writeReg RVBAR_EL3 w__419
  let w__420 ← (( do (undefined_HSTR_EL2_Type (.site 8036) ()) ) : SailM (BitVec 64) )
  writeReg HSTR_EL2 w__420
  let w__421 ← (( do (undefined_MDSELR_EL1_Type (.site 8037) ()) ) : SailM (BitVec 64) )
  writeReg MDSELR_EL1 w__421
  let w__422 ← (( do (undefined_bitvector_at (.site 8038) 64) ) : SailM (BitVec 64) )
  let w__423 ← (( do (undefined_vector 32 w__422) ) : SailM (Vector (BitVec 64) 32) )
  writeReg PMEVCNTR_EL0 w__423
  let w__424 ← (( do (undefined_PMCCNTR_EL0_Type (.site 8039) ()) ) : SailM (BitVec 64) )
  writeReg PMCCNTR_EL0 w__424
  let w__425 ← (( do (undefined_PMSICR_EL1_Type (.site 8040) ()) ) : SailM (BitVec 64) )
  writeReg PMSICR_EL1 w__425
  let w__426 ← (( do (undefined_PMSIRR_EL1_Type (.site 8041) ()) ) : SailM (BitVec 64) )
  writeReg PMSIRR_EL1 w__426
  let w__427 ← (( do (undefined_PMBPTR_EL1_Type (.site 8042) ()) ) : SailM (BitVec 64) )
  writeReg PMBPTR_EL1 w__427
  let w__428 ← (( do (undefined_PMSDSFR_EL1_Type (.site 8043) ()) ) : SailM (BitVec 64) )
  writeReg PMSDSFR_EL1 w__428
  let w__429 ← (( do (undefined_PMSEVFR_EL1_Type (.site 8044) ()) ) : SailM (BitVec 64) )
  writeReg PMSEVFR_EL1 w__429
  let w__430 ← (( do (undefined_PMSFCR_EL1_Type (.site 8045) ()) ) : SailM (BitVec 64) )
  writeReg PMSFCR_EL1 w__430
  let w__431 ← (( do (undefined_PMSLATFR_EL1_Type (.site 8046) ()) ) : SailM (BitVec 64) )
  writeReg PMSLATFR_EL1 w__431
  let w__432 ← (( do (undefined_PMSNEVFR_EL1_Type (.site 8047) ()) ) : SailM (BitVec 64) )
  writeReg PMSNEVFR_EL1 w__432
  let w__433 ← (( do (undefined_PMBIDR_EL1_Type (.site 8048) ()) ) : SailM (BitVec 64) )
  writeReg PMBIDR_EL1 w__433
  let w__434 ← (( do (undefined_bitvector_at (.site 8049) 8) ) : SailM (BitVec 8) )
  let w__435 ← (( do (undefined_vector 64 w__434) ) : SailM (Vector (BitVec 8) 64) )
  writeReg SPERecordData w__435
  let w__436 ← (( do (undefined_int_at (.site 8050) ()) ) : SailM Int )
  let w__437 ← (( do (undefined_vector 32 w__436) ) : SailM (Vector Int 32) )
  writeReg SPESampleCounter w__437
  let w__438 ← (( do (undefined_BRBINFINJ_EL1_Type (.site 8051) ()) ) : SailM (BitVec 64) )
  writeReg BRBINFINJ_EL1 w__438
  let w__439 ← (( do (undefined_BRBSRCINJ_EL1_Type (.site 8052) ()) ) : SailM (BitVec 64) )
  writeReg BRBSRCINJ_EL1 w__439
  let w__440 ← (( do (undefined_BRBTGTINJ_EL1_Type (.site 8053) ()) ) : SailM (BitVec 64) )
  writeReg BRBTGTINJ_EL1 w__440
  let w__441 ← (( do (undefined_DCZID_EL0_Type (.site 8054) ()) ) : SailM (BitVec 64) )
  writeReg DCZID_EL0 w__441
  let w__442 ← (( do (undefined_PRRR_Type (.site 8055) ()) ) : SailM (BitVec 32) )
  writeReg _PRRR_NS w__442
  let w__443 ← (( do (undefined_PRRR_Type (.site 8056) ()) ) : SailM (BitVec 32) )
  writeReg PRRR_S w__443
  let w__444 ← (( do (undefined_MAIR0_Type (.site 8057) ()) ) : SailM (BitVec 32) )
  writeReg _MAIR0_NS w__444
  let w__445 ← (( do (undefined_MAIR0_Type (.site 8058) ()) ) : SailM (BitVec 32) )
  writeReg _MAIR0_S w__445
  let w__446 ← (( do (undefined_NMRR_Type (.site 8059) ()) ) : SailM (BitVec 32) )
  writeReg _NMRR_NS w__446
  let w__447 ← (( do (undefined_NMRR_Type (.site 8060) ()) ) : SailM (BitVec 32) )
  writeReg NMRR_S w__447
  let w__448 ← (( do (undefined_MAIR1_Type (.site 8061) ()) ) : SailM (BitVec 32) )
  writeReg _MAIR1_NS w__448
  let w__449 ← (( do (undefined_MAIR1_Type (.site 8062) ()) ) : SailM (BitVec 32) )
  writeReg _MAIR1_S w__449
  let w__450 ← (( do (undefined_TTBCR2_Type (.site 8063) ()) ) : SailM (BitVec 32) )
  writeReg _TTBCR2_NS w__450
  let w__451 ← (( do (undefined_TTBCR2_Type (.site 8064) ()) ) : SailM (BitVec 32) )
  writeReg TTBCR2_S w__451
  let w__452 ← (( do (undefined_HMAIR0_Type (.site 8065) ()) ) : SailM (BitVec 32) )
  writeReg _HMAIR0 w__452
  let w__453 ← (( do (undefined_HMAIR1_Type (.site 8066) ()) ) : SailM (BitVec 32) )
  writeReg _HMAIR1 w__453
  let w__454 ← (( do (undefined_HTCR_Type (.site 8067) ()) ) : SailM (BitVec 32) )
  writeReg _HTCR w__454
  let w__455 ← (( do (undefined_VTCR_Type (.site 8068) ()) ) : SailM (BitVec 32) )
  writeReg _VTCR w__455
  let w__456 ← (( do (undefined_DACR32_EL2_Type (.site 8069) ()) ) : SailM (BitVec 64) )
  writeReg DACR32_EL2 w__456
  let w__457 ← (( do (undefined_DACR_Type (.site 8070) ()) ) : SailM (BitVec 32) )
  writeReg _DACR_NS w__457
  let w__458 ← (( do (undefined_DACR_Type (.site 8071) ()) ) : SailM (BitVec 32) )
  writeReg DACR_S w__458
  let w__459 ← (( do (undefined_PAR_Type (.site 8072) ()) ) : SailM (BitVec 64) )
  writeReg PAR_NS w__459

def initialize_registers_9 (_ : Unit) : SailM Unit := do
  let w__460 ← (( do (undefined_PAR_Type (.site 8073) ()) ) : SailM (BitVec 64) )
  writeReg PAR_S w__460
  let w__461 ← (( do (undefined_PAR_EL1_Type (.site 8074) ()) ) : SailM (BitVec 128) )
  writeReg _PAR_EL1 w__461
  let w__462 ← (( do (undefined_CTILSR_Type (.site 8075) ()) ) : SailM (BitVec 32) )
  writeReg CTILSR w__462
  let w__463 ← (( do (undefined_EDLSR_Type (.site 8076) ()) ) : SailM (BitVec 32) )
  writeReg EDLSR w__463
  let w__464 ← (( do (undefined_PMLSR_Type (.site 8077) ()) ) : SailM (BitVec 32) )
  writeReg PMLSR w__464
  let w__465 ← (( do (undefined_bitvector_at (.site 8078) 64) ) : SailM (BitVec 64) )
  writeReg DBGDTRRX_EL0 w__465
  let w__466 ← (( do (undefined_bitvector_at (.site 8079) 64) ) : SailM (BitVec 64) )
  writeReg DBGDTRTX_EL0 w__466
  let w__467 ← (( do (undefined_DBGDTR_EL0_Type (.site 8080) ()) ) : SailM (BitVec 64) )
  writeReg _DBGDTR_EL0 w__467
  let w__468 ← (( do (undefined_EDPRSR_Type (.site 8081) ()) ) : SailM (BitVec 32) )
  writeReg EDPRSR w__468
  let w__469 ← (( do (undefined_MDCCINT_EL1_Type (.site 8082) ()) ) : SailM (BitVec 64) )
  writeReg MDCCINT_EL1 w__469
  let w__470 ← (( do (undefined_DBGDCCINT_Type (.site 8083) ()) ) : SailM (BitVec 32) )
  writeReg _DBGDCCINT w__470
  let w__471 ← (( do (undefined_CTIDEVCTL_Type (.site 8084) ()) ) : SailM (BitVec 32) )
  writeReg CTIDEVCTL w__471
  let w__472 ← (( do (undefined_EDVIDSR_Type (.site 8085) ()) ) : SailM (BitVec 32) )
  writeReg EDVIDSR w__472
  let w__473 ← (( do (undefined_PMPCSR_Type (.site 8086) ()) ) : SailM (BitVec 64) )
  writeReg PMPCSR w__473
  let w__474 ← (( do (undefined_PMVIDSR_Type (.site 8087) ()) ) : SailM (BitVec 32) )
  writeReg PMVIDSR w__474
  let w__475 ← (( do (undefined_TRFCR_EL2_Type (.site 8088) ()) ) : SailM (BitVec 64) )
  writeReg TRFCR_EL2 w__475
  let w__476 ← (( do (undefined_HTRFCR_Type (.site 8089) ()) ) : SailM (BitVec 32) )
  writeReg _HTRFCR w__476
  let w__477 ← (( do (undefined_TRFCR_EL1_Type (.site 8090) ()) ) : SailM (BitVec 64) )
  writeReg TRFCR_EL1 w__477
  let w__478 ← (( do (undefined_TRFCR_Type (.site 8091) ()) ) : SailM (BitVec 32) )
  writeReg _TRFCR w__478
  let w__479 ← (( do (undefined_DBGBCR_Type (.site 8092) ()) ) : SailM (BitVec 32) )
  let w__480 ← (( do (undefined_vector 16 w__479) ) : SailM (Vector (BitVec 32) 16) )
  writeReg _DBGBCR w__480
  let w__481 ← (( do (undefined_DBGBVR_Type (.site 8093) ()) ) : SailM (BitVec 32) )
  let w__482 ← (( do (undefined_vector 16 w__481) ) : SailM (Vector (BitVec 32) 16) )
  writeReg _DBGBVR w__482
  let w__483 ← (( do (undefined_DBGBXVR_Type (.site 8094) ()) ) : SailM (BitVec 32) )
  let w__484 ← (( do (undefined_vector 16 w__483) ) : SailM (Vector (BitVec 32) 16) )
  writeReg _DBGBXVR w__484
  let w__485 ← (( do (undefined_DBGVCR32_EL2_Type (.site 8095) ()) ) : SailM (BitVec 64) )
  writeReg DBGVCR32_EL2 w__485
  let w__486 ← (( do (undefined_DBGVCR_Type (.site 8096) ()) ) : SailM (BitVec 32) )
  writeReg _DBGVCR w__486
  let w__487 ← (( do (undefined_DBGWCR_Type (.site 8097) ()) ) : SailM (BitVec 32) )
  let w__488 ← (( do (undefined_vector 16 w__487) ) : SailM (Vector (BitVec 32) 16) )
  writeReg _DBGWCR w__488
  let w__489 ← (( do (undefined_DBGWVR_Type (.site 8098) ()) ) : SailM (BitVec 32) )
  let w__490 ← (( do (undefined_vector 16 w__489) ) : SailM (Vector (BitVec 32) 16) )
  writeReg _DBGWVR w__490
  let w__491 ← (( do (undefined_HSTR_Type (.site 8099) ()) ) : SailM (BitVec 32) )
  writeReg _HSTR w__491
  let w__492 ← (( do (undefined_bitvector_at (.site 8100) 32) ) : SailM (BitVec 32) )
  let w__493 ← (( do (undefined_vector 31 w__492) ) : SailM (Vector (BitVec 32) 31) )
  writeReg _PMEVCNTR w__493
  let w__494 ← (( do (undefined_PMOVSSET_Type (.site 8101) ()) ) : SailM (BitVec 32) )
  writeReg _PMOVSSET w__494
  let w__495 ← (( do (undefined_PMCCNTR_Type (.site 8102) ()) ) : SailM (BitVec 64) )
  writeReg _PMCCNTR w__495
  let w__496 ← (( do (undefined_ID_MMFR2_EL1_Type (.site 8103) ()) ) : SailM (BitVec 64) )
  writeReg ID_MMFR2_EL1 w__496
  let w__497 ← (( do (undefined_ID_MMFR4_EL1_Type (.site 8104) ()) ) : SailM (BitVec 64) )
  writeReg ID_MMFR4_EL1 w__497
  let w__498 ← (( do (undefined_ID_AA64MMFR2_EL1_Type (.site 8105) ()) ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR2_EL1 w__498
  let w__499 ← (( do (undefined_HDFGRTR_EL2_Type (.site 8106) ()) ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 w__499
  let w__500 ← (( do (undefined_ICV_NMIAR1_EL1_Type (.site 8107) ()) ) : SailM (BitVec 64) )
  writeReg ICV_NMIAR1_EL1 w__500
  let w__501 ← (( do (undefined_ICH_LR_EL2_Type (.site 8108) ()) ) : SailM (BitVec 64) )
  let w__502 ← (( do (undefined_vector 16 w__501) ) : SailM (Vector (BitVec 64) 16) )
  writeReg ICH_LR_EL2 w__502
  let w__503 ← (( do (undefined_MVFR0_EL1_Type (.site 8109) ()) ) : SailM (BitVec 64) )
  writeReg MVFR0_EL1 w__503
  let w__504 ← (( do (undefined_ICC_HPPIR1_EL1_Type (.site 8110) ()) ) : SailM (BitVec 64) )
  writeReg ICC_HPPIR1_EL1 w__504
  let w__505 ← (( do (undefined_bitvector_at (.site 8111) 64) ) : SailM (BitVec 64) )
  let w__506 ← (( do (undefined_vector 4 w__505) ) : SailM (Vector (BitVec 64) 4) )
  writeReg ICC_AP0R_EL1 w__506
  let w__507 ← (( do (undefined_ID_AA64DFR0_EL1_Type (.site 8112) ()) ) : SailM (BitVec 64) )
  writeReg ID_AA64DFR0_EL1 w__507
  let w__508 ← (( do (undefined_ICV_BPR1_EL1_Type (.site 8113) ()) ) : SailM (BitVec 64) )
  writeReg ICV_BPR1_EL1 w__508
  let w__509 ← (( do (undefined_ID_ISAR2_EL1_Type (.site 8114) ()) ) : SailM (BitVec 64) )
  writeReg ID_ISAR2_EL1 w__509
  let w__510 ← (( do (undefined_PMECR_EL1_Type (.site 8115) ()) ) : SailM (BitVec 64) )
  writeReg PMECR_EL1 w__510
  let w__511 ← (( do (undefined_bitvector_at (.site 8116) 64) ) : SailM (BitVec 64) )
  writeReg AIDR_EL1 w__511
  let w__512 ← (( do (undefined_ICV_EOIR1_EL1_Type (.site 8117) ()) ) : SailM (BitVec 64) )
  writeReg ICV_EOIR1_EL1 w__512
  let w__513 ← (( do (undefined_RMR_EL1_Type (.site 8118) ()) ) : SailM (BitVec 64) )
  writeReg RMR_EL1 w__513
  let w__514 ← (( do (undefined_OSLAR_EL1_Type (.site 8119) ()) ) : SailM (BitVec 64) )
  writeReg OSLAR_EL1 w__514
  let w__515 ← (( do (undefined_ICC_HPPIR0_EL1_Type (.site 8120) ()) ) : SailM (BitVec 64) )
  writeReg ICC_HPPIR0_EL1 w__515

def initialize_registers_10 (_ : Unit) : SailM Unit := do
  let w__516 ← (( do (undefined_HAFGRTR_EL2_Type (.site 8121) ()) ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 w__516
  let w__517 ← (( do (undefined_ICC_BPR0_EL1_Type (.site 8122) ()) ) : SailM (BitVec 64) )
  writeReg ICC_BPR0_EL1 w__517
  let w__518 ← (( do (undefined_ID_AA64DFR1_EL1_Type (.site 8123) ()) ) : SailM (BitVec 64) )
  writeReg ID_AA64DFR1_EL1 w__518
  let w__519 ← (( do (undefined_ACCDATA_EL1_Type (.site 8124) ()) ) : SailM (BitVec 64) )
  writeReg ACCDATA_EL1 w__519
  let w__520 ← (( do (undefined_bitvector_at (.site 8125) 64) ) : SailM (BitVec 64) )
  writeReg REVIDR_EL1 w__520
  let w__521 ← (( do (undefined_PMSSCR_EL1_Type (.site 8126) ()) ) : SailM (BitVec 64) )
  writeReg PMSSCR_EL1 w__521
  let w__522 ← (( do (undefined_LORID_EL1_Type (.site 8127) ()) ) : SailM (BitVec 64) )
  writeReg LORID_EL1 w__522
  let w__523 ← (( do (undefined_bitvector_at (.site 8128) 64) ) : SailM (BitVec 64) )
  writeReg TPIDR_EL2 w__523
  let w__524 ← (( do (undefined_CNTP_TVAL_EL0_Type (.site 8129) ()) ) : SailM (BitVec 64) )
  writeReg CNTP_TVAL_EL0 w__524
  let w__525 ← (( do (undefined_ID_AA64ISAR1_EL1_Type (.site 8130) ()) ) : SailM (BitVec 64) )
  writeReg ID_AA64ISAR1_EL1 w__525
  let w__526 ← (( do (undefined_ID_AA64MMFR4_EL1_Type (.site 8131) ()) ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR4_EL1 w__526
  let w__527 ← (( do (undefined_bitvector_at (.site 8132) 64) ) : SailM (BitVec 64) )
  writeReg ACTLR_EL2 w__527
  let w__528 ← (( do (undefined_ICH_EISR_EL2_Type (.site 8133) ()) ) : SailM (BitVec 64) )
  writeReg ICH_EISR_EL2 w__528
  let w__529 ← (( do (undefined_MIDR_EL1_Type (.site 8134) ()) ) : SailM (BitVec 64) )
  writeReg MIDR_EL1 w__529
  let w__530 ← (( do (undefined_ICC_RPR_EL1_Type (.site 8135) ()) ) : SailM (BitVec 64) )
  writeReg ICC_RPR_EL1 w__530
  let w__531 ← (( do (undefined_ICH_ELRSR_EL2_Type (.site 8136) ()) ) : SailM (BitVec 64) )
  writeReg ICH_ELRSR_EL2 w__531
  let w__532 ← (( do (undefined_ICC_SGI0R_EL1_Type (.site 8137) ()) ) : SailM (BitVec 64) )
  writeReg ICC_SGI0R_EL1 w__532
  let w__533 ← (( do (undefined_SPMACCESSR_EL1_Type (.site 8138) ()) ) : SailM (BitVec 64) )
  writeReg SPMACCESSR_EL1 w__533
  let w__534 ← (( do (undefined_SPMSELR_EL0_Type (.site 8139) ()) ) : SailM (BitVec 64) )
  writeReg SPMSELR_EL0 w__534
  let w__535 ← (( do (undefined_ID_AA64PFR1_EL1_Type (.site 8140) ()) ) : SailM (BitVec 64) )
  writeReg ID_AA64PFR1_EL1 w__535
  let w__536 ← (( do (undefined_ID_AA64PFR0_EL1_Type (.site 8141) ()) ) : SailM (BitVec 64) )
  writeReg ID_AA64PFR0_EL1 w__536
  let w__537 ← (( do (undefined_ICH_AP1R_EL2_Type (.site 8142) ()) ) : SailM (BitVec 64) )
  let w__538 ← (( do (undefined_vector 4 w__537) ) : SailM (Vector (BitVec 64) 4) )
  writeReg ICH_AP1R_EL2 w__538
  let w__539 ← (( do (undefined_ICC_DIR_EL1_Type (.site 8143) ()) ) : SailM (BitVec 64) )
  writeReg ICC_DIR_EL1 w__539
  let w__540 ← (( do (undefined_PMEVCNTSVR_EL1_Type (.site 8144) ()) ) : SailM (BitVec 64) )
  let w__541 ← (( do (undefined_vector 31 w__540) ) : SailM (Vector (BitVec 64) 31) )
  writeReg PMEVCNTSVR_EL1 w__541
  let w__542 ← (( do (undefined_ID_AA64ISAR0_EL1_Type (.site 8145) ()) ) : SailM (BitVec 64) )
  writeReg ID_AA64ISAR0_EL1 w__542
  let w__543 ← (( do (undefined_PMMIR_EL1_Type (.site 8146) ()) ) : SailM (BitVec 64) )
  writeReg PMMIR_EL1 w__543
  let w__544 ← (( do (undefined_ICV_IAR0_EL1_Type (.site 8147) ()) ) : SailM (BitVec 64) )
  writeReg ICV_IAR0_EL1 w__544
  let w__545 ← (( do (undefined_ICC_IGRPEN1_EL1_Type (.site 8148) ()) ) : SailM (BitVec 64) )
  writeReg ICC_IGRPEN1_EL1_S w__545
  let w__546 ← (( do (undefined_ICC_IGRPEN1_EL1_Type (.site 8149) ()) ) : SailM (BitVec 64) )
  writeReg ICC_IGRPEN1_EL1_NS w__546
  let w__547 ← (( do (undefined_ID_MMFR5_EL1_Type (.site 8150) ()) ) : SailM (BitVec 64) )
  writeReg ID_MMFR5_EL1 w__547
  let w__548 ← (( do (undefined_ICC_NMIAR1_EL1_Type (.site 8151) ()) ) : SailM (BitVec 64) )
  writeReg ICC_NMIAR1_EL1 w__548
  let w__549 ← (( do (undefined_DBGCLAIMSET_EL1_Type (.site 8152) ()) ) : SailM (BitVec 64) )
  writeReg DBGCLAIMSET_EL1 w__549
  let w__550 ← (( do (undefined_ICC_SRE_EL1_Type (.site 8153) ()) ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL1_S w__550
  let w__551 ← (( do (undefined_ICC_SRE_EL1_Type (.site 8154) ()) ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL1_NS w__551
  let w__552 ← (( do (undefined_ICH_AP0R_EL2_Type (.site 8155) ()) ) : SailM (BitVec 64) )
  let w__553 ← (( do (undefined_vector 4 w__552) ) : SailM (Vector (BitVec 64) 4) )
  writeReg ICH_AP0R_EL2 w__553
  let w__554 ← (( do (undefined_ICC_IAR0_EL1_Type (.site 8156) ()) ) : SailM (BitVec 64) )
  writeReg ICC_IAR0_EL1 w__554
  let w__555 ← (( do (undefined_bitvector_at (.site 8157) 64) ) : SailM (BitVec 64) )
  writeReg TPIDR_EL1 w__555
  let w__556 ← (( do (undefined_ID_ISAR4_EL1_Type (.site 8158) ()) ) : SailM (BitVec 64) )
  writeReg ID_ISAR4_EL1 w__556
  let w__557 ← (( do (undefined_ID_ISAR1_EL1_Type (.site 8159) ()) ) : SailM (BitVec 64) )
  writeReg ID_ISAR1_EL1 w__557
  let w__558 ← (( do (undefined_PMUACR_EL1_Type (.site 8160) ()) ) : SailM (BitVec 64) )
  writeReg PMUACR_EL1 w__558
  let w__559 ← (( do (undefined_bitvector_at (.site 8161) 64) ) : SailM (BitVec 64) )
  writeReg ACTLR_EL1 w__559
  let w__560 ← (( do (undefined_RMR_EL2_Type (.site 8162) ()) ) : SailM (BitVec 64) )
  writeReg RMR_EL2 w__560
  let w__561 ← (( do (undefined_PMSELR_EL0_Type (.site 8163) ()) ) : SailM (BitVec 64) )
  writeReg PMSELR_EL0 w__561
  let w__562 ← (( do (undefined_ICC_CTLR_EL1_Type (.site 8164) ()) ) : SailM (BitVec 64) )
  writeReg ICC_CTLR_EL1_S w__562
  let w__563 ← (( do (undefined_ICC_CTLR_EL1_Type (.site 8165) ()) ) : SailM (BitVec 64) )
  writeReg ICC_CTLR_EL1_NS w__563
  let w__564 ← (( do (undefined_ID_ISAR6_EL1_Type (.site 8166) ()) ) : SailM (BitVec 64) )
  writeReg ID_ISAR6_EL1 w__564
  let w__565 ← (( do (undefined_ICC_AP1R_EL1_Type (.site 8167) ()) ) : SailM (BitVec 64) )
  let w__566 ← (( do (undefined_vector 4 w__565) ) : SailM (Vector (BitVec 64) 4) )
  writeReg ICC_AP1R_EL1_S w__566
  let w__567 ← (( do (undefined_ICC_AP1R_EL1_Type (.site 8168) ()) ) : SailM (BitVec 64) )
  let w__568 ← (( do (undefined_vector 4 w__567) ) : SailM (Vector (BitVec 64) 4) )
  writeReg ICC_AP1R_EL1_NS w__568

def initialize_registers_11 (_ : Unit) : SailM Unit := do
  let w__569 ← (( do (undefined_bitvector_at (.site 8169) 64) ) : SailM (BitVec 64) )
  writeReg HFGITR2_EL2 w__569
  let w__570 ← (( do (undefined_CNTHV_TVAL_EL2_Type (.site 8170) ()) ) : SailM (BitVec 64) )
  writeReg CNTHV_TVAL_EL2 w__570
  let w__571 ← (( do (undefined_ICH_MISR_EL2_Type (.site 8171) ()) ) : SailM (BitVec 64) )
  writeReg ICH_MISR_EL2 w__571
  let w__572 ← (( do (undefined_CSSELR_EL1_Type (.site 8172) ()) ) : SailM (BitVec 64) )
  writeReg CSSELR_EL1 w__572
  let w__573 ← (( do (undefined_ICV_RPR_EL1_Type (.site 8173) ()) ) : SailM (BitVec 64) )
  writeReg ICV_RPR_EL1 w__573
  let w__574 ← (( do (undefined_ICV_PMR_EL1_Type (.site 8174) ()) ) : SailM (BitVec 64) )
  writeReg ICV_PMR_EL1 w__574
  let w__575 ← (( do (undefined_ICV_HPPIR0_EL1_Type (.site 8175) ()) ) : SailM (BitVec 64) )
  writeReg ICV_HPPIR0_EL1 w__575
  let w__576 ← (( do (undefined_ICV_BPR0_EL1_Type (.site 8176) ()) ) : SailM (BitVec 64) )
  writeReg ICV_BPR0_EL1 w__576
  let w__577 ← (( do (undefined_ISR_EL1_Type (.site 8177) ()) ) : SailM (BitVec 64) )
  writeReg ISR_EL1 w__577
  let w__578 ← (( do (undefined_ID_ISAR3_EL1_Type (.site 8178) ()) ) : SailM (BitVec 64) )
  writeReg ID_ISAR3_EL1 w__578
  let w__579 ← (( do (undefined_bitvector_at (.site 8179) 64) ) : SailM (BitVec 64) )
  writeReg AFSR1_EL1 w__579
  let w__580 ← (( do (undefined_PMCCNTSVR_EL1_Type (.site 8180) ()) ) : SailM (BitVec 64) )
  writeReg PMCCNTSVR_EL1 w__580
  let w__581 ← (( do (undefined_MECIDR_EL2_Type (.site 8181) ()) ) : SailM (BitVec 64) )
  writeReg MECIDR_EL2 w__581
  let w__582 ← (( do (undefined_PMINTENSET_EL1_Type (.site 8182) ()) ) : SailM (BitVec 64) )
  writeReg PMINTENSET_EL1 w__582
  let w__583 ← (( do (undefined_SMIDR_EL1_Type (.site 8183) ()) ) : SailM (BitVec 64) )
  writeReg SMIDR_EL1 w__583
  let w__584 ← (( do (undefined_HFGWTR_EL2_Type (.site 8184) ()) ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 w__584
  let w__585 ← (( do (undefined_SMPRI_EL1_Type (.site 8185) ()) ) : SailM (BitVec 64) )
  writeReg SMPRI_EL1 w__585
  let w__586 ← (( do (undefined_PMUSERENR_EL0_Type (.site 8186) ()) ) : SailM (BitVec 64) )
  writeReg PMUSERENR_EL0 w__586
  let w__587 ← (( do (undefined_bitvector_at (.site 8187) 64) ) : SailM (BitVec 64) )
  writeReg AMAIR2_EL2 w__587
  let w__588 ← (( do (undefined_bitvector_at (.site 8188) 64) ) : SailM (BitVec 64) )
  let w__589 ← (( do (undefined_vector 4 w__588) ) : SailM (Vector (BitVec 64) 4) )
  writeReg ICV_AP0R_EL1 w__589
  let w__590 ← (( do (undefined_bitvector_at (.site 8189) 64) ) : SailM (BitVec 64) )
  writeReg AFSR0_EL3 w__590
  let w__591 ← (( do (undefined_bitvector_at (.site 8190) 64) ) : SailM (BitVec 64) )
  writeReg CNTFRQ_EL0 w__591
  let w__592 ← (( do (undefined_ICV_CTLR_EL1_Type (.site 8191) ()) ) : SailM (BitVec 64) )
  writeReg ICV_CTLR_EL1 w__592
  let w__593 ← (( do (undefined_bitvector_at (.site 8192) 64) ) : SailM (BitVec 64) )
  writeReg AFSR1_EL2 w__593
  let w__594 ← (( do (undefined_ICV_IAR1_EL1_Type (.site 8193) ()) ) : SailM (BitVec 64) )
  writeReg ICV_IAR1_EL1 w__594
  let w__595 ← (( do (undefined_ID_PFR0_EL1_Type (.site 8194) ()) ) : SailM (BitVec 64) )
  writeReg ID_PFR0_EL1 w__595
  let w__596 ← (( do (undefined_MVFR1_EL1_Type (.site 8195) ()) ) : SailM (BitVec 64) )
  writeReg MVFR1_EL1 w__596
  let w__597 ← (( do (undefined_HDFGWTR2_EL2_Type (.site 8196) ()) ) : SailM (BitVec 64) )
  writeReg HDFGWTR2_EL2 w__597
  let w__598 ← (( do (undefined_ID_ISAR0_EL1_Type (.site 8197) ()) ) : SailM (BitVec 64) )
  writeReg ID_ISAR0_EL1 w__598
  let w__599 ← (( do (undefined_bitvector_at (.site 8198) 64) ) : SailM (BitVec 64) )
  writeReg AFSR0_EL1 w__599
  let w__600 ← (( do (undefined_CNTHVS_TVAL_EL2_Type (.site 8199) ()) ) : SailM (BitVec 64) )
  writeReg CNTHVS_TVAL_EL2 w__600
  let w__601 ← (( do (undefined_CNTHP_TVAL_EL2_Type (.site 8200) ()) ) : SailM (BitVec 64) )
  writeReg CNTHP_TVAL_EL2 w__601
  let w__602 ← (( do (undefined_SPMACCESSR_EL2_Type (.site 8201) ()) ) : SailM (BitVec 64) )
  writeReg SPMACCESSR_EL2 w__602
  let w__603 ← (( do (undefined_PMZR_EL0_Type (.site 8202) ()) ) : SailM (BitVec 64) )
  writeReg PMZR_EL0 w__603
  let w__604 ← (( do (undefined_PMICNTSVR_EL1_Type (.site 8203) ()) ) : SailM (BitVec 64) )
  writeReg PMICNTSVR_EL1 w__604
  let w__605 ← (( do (undefined_MDRAR_EL1_Type (.site 8204) ()) ) : SailM (BitVec 64) )
  writeReg MDRAR_EL1 w__605
  let w__606 ← (( do (undefined_bitvector_at (.site 8205) 64) ) : SailM (BitVec 64) )
  writeReg OSDTRRX_EL1 w__606
  let w__607 ← (( do (undefined_ICC_IGRPEN1_EL3_Type (.site 8206) ()) ) : SailM (BitVec 64) )
  writeReg ICC_IGRPEN1_EL3 w__607
  let w__608 ← (( do (undefined_ID_MMFR1_EL1_Type (.site 8207) ()) ) : SailM (BitVec 64) )
  writeReg ID_MMFR1_EL1 w__608
  let w__609 ← (( do (undefined_LORSA_EL1_Type (.site 8208) ()) ) : SailM (BitVec 64) )
  writeReg LORSA_EL1 w__609
  let w__610 ← (( do (undefined_ID_AA64MMFR1_EL1_Type (.site 8209) ()) ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR1_EL1 w__610
  let w__611 ← (( do (undefined_PMSWINC_EL0_Type (.site 8210) ()) ) : SailM (BitVec 64) )
  writeReg PMSWINC_EL0 w__611
  let w__612 ← (( do (undefined_bitvector_at (.site 8211) 64) ) : SailM (BitVec 64) )
  writeReg SCXTNUM_EL2 w__612
  let w__613 ← (( do (undefined_PMIAR_EL1_Type (.site 8212) ()) ) : SailM (BitVec 64) )
  writeReg PMIAR_EL1 w__613
  let w__614 ← (( do (undefined_bitvector_at (.site 8213) 64) ) : SailM (BitVec 64) )
  writeReg TPIDR_EL3 w__614
  let w__615 ← (( do (undefined_ID_MMFR0_EL1_Type (.site 8214) ()) ) : SailM (BitVec 64) )
  writeReg ID_MMFR0_EL1 w__615
  let w__616 ← (( do (undefined_bitvector_at (.site 8215) 64) ) : SailM (BitVec 64) )
  writeReg OSDTRTX_EL1 w__616
  let w__617 ← (( do (undefined_ICH_VMCR_EL2_Type (.site 8216) ()) ) : SailM (BitVec 64) )
  writeReg ICH_VMCR_EL2 w__617

def initialize_registers_12 (_ : Unit) : SailM Unit := do
  let w__618 ← (( do (undefined_VPIDR_EL2_Type (.site 8217) ()) ) : SailM (BitVec 64) )
  writeReg VPIDR_EL2 w__618
  let w__619 ← (( do (undefined_bitvector_at (.site 8218) 64) ) : SailM (BitVec 64) )
  writeReg ACTLR_EL3 w__619
  let w__620 ← (( do (undefined_ICC_CTLR_EL3_Type (.site 8219) ()) ) : SailM (BitVec 64) )
  writeReg ICC_CTLR_EL3 w__620
  let w__621 ← (( do (undefined_bitvector_at (.site 8220) 64) ) : SailM (BitVec 64) )
  writeReg AMAIR_EL2 w__621
  let w__622 ← (( do (undefined_bitvector_at (.site 8221) 64) ) : SailM (BitVec 64) )
  writeReg AMAIR_EL3 w__622
  let w__623 ← (( do (undefined_ICC_SRE_EL2_Type (.site 8222) ()) ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL2 w__623
  let w__624 ← (( do (undefined_LORC_EL1_Type (.site 8223) ()) ) : SailM (BitVec 64) )
  writeReg LORC_EL1 w__624
  let w__625 ← (( do (undefined_ID_AA64PFR2_EL1_Type (.site 8224) ()) ) : SailM (BitVec 64) )
  writeReg ID_AA64PFR2_EL1 w__625
  let w__626 ← (( do (undefined_bitvector_at (.site 8225) 64) ) : SailM (BitVec 64) )
  writeReg SCXTNUM_EL1 w__626
  let w__627 ← (( do (undefined_CCSIDR2_EL1_Type (.site 8226) ()) ) : SailM (BitVec 64) )
  writeReg CCSIDR2_EL1 w__627
  let w__628 ← (( do (undefined_ICC_ASGI1R_EL1_Type (.site 8227) ()) ) : SailM (BitVec 64) )
  writeReg ICC_ASGI1R_EL1 w__628
  let w__629 ← (( do (undefined_ID_AA64ISAR2_EL1_Type (.site 8228) ()) ) : SailM (BitVec 64) )
  writeReg ID_AA64ISAR2_EL1 w__629
  let w__630 ← (( do (undefined_HFGRTR2_EL2_Type (.site 8229) ()) ) : SailM (BitVec 64) )
  writeReg HFGRTR2_EL2 w__630
  let w__631 ← (( do (undefined_bitvector_at (.site 8230) 64) ) : SailM (BitVec 64) )
  writeReg TPIDRRO_EL0 w__631
  let w__632 ← (( do (undefined_ID_ISAR5_EL1_Type (.site 8231) ()) ) : SailM (BitVec 64) )
  writeReg ID_ISAR5_EL1 w__632
  let w__633 ← (( do (undefined_RMR_EL3_Type (.site 8232) ()) ) : SailM (BitVec 64) )
  writeReg RMR_EL3 w__633
  let w__634 ← (( do (undefined_ICH_HCR_EL2_Type (.site 8233) ()) ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 w__634
  let w__635 ← (( do (undefined_ICC_IGRPEN0_EL1_Type (.site 8234) ()) ) : SailM (BitVec 64) )
  writeReg ICC_IGRPEN0_EL1 w__635
  let w__636 ← (( do (undefined_CNTHPS_TVAL_EL2_Type (.site 8235) ()) ) : SailM (BitVec 64) )
  writeReg CNTHPS_TVAL_EL2 w__636
  let w__637 ← (( do (undefined_ICC_BPR1_EL1_Type (.site 8236) ()) ) : SailM (BitVec 64) )
  writeReg ICC_BPR1_EL1_S w__637
  let w__638 ← (( do (undefined_ICC_BPR1_EL1_Type (.site 8237) ()) ) : SailM (BitVec 64) )
  writeReg ICC_BPR1_EL1_NS w__638
  let w__639 ← (( do (undefined_bitvector_at (.site 8238) 64) ) : SailM (BitVec 64) )
  writeReg AMAIR_EL1 w__639
  let w__640 ← (( do (undefined_bitvector_at (.site 8239) 64) ) : SailM (BitVec 64) )
  writeReg SCXTNUM_EL0 w__640
  let w__641 ← (( do (undefined_ICC_EOIR1_EL1_Type (.site 8240) ()) ) : SailM (BitVec 64) )
  writeReg ICC_EOIR1_EL1 w__641
  let w__642 ← (( do (undefined_ID_AA64MMFR0_EL1_Type (.site 8241) ()) ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR0_EL1 w__642
  let w__643 ← (( do (undefined_bitvector_at (.site 8242) 64) ) : SailM (BitVec 64) )
  writeReg TPIDR2_EL0 w__643
  let w__644 ← (( do (undefined_HDFGRTR2_EL2_Type (.site 8243) ()) ) : SailM (BitVec 64) )
  writeReg HDFGRTR2_EL2 w__644
  let w__645 ← (( do (undefined_VMPIDR_EL2_Type (.site 8244) ()) ) : SailM (BitVec 64) )
  writeReg VMPIDR_EL2 w__645
  let w__646 ← (( do (undefined_ID_AA64MMFR3_EL1_Type (.site 8245) ()) ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR3_EL1 w__646
  let w__647 ← (( do (undefined_ICH_VTR_EL2_Type (.site 8246) ()) ) : SailM (BitVec 64) )
  writeReg ICH_VTR_EL2 w__647
  let w__648 ← (( do (undefined_ID_PFR1_EL1_Type (.site 8247) ()) ) : SailM (BitVec 64) )
  writeReg ID_PFR1_EL1 w__648
  let w__649 ← (( do (undefined_ICV_EOIR0_EL1_Type (.site 8248) ()) ) : SailM (BitVec 64) )
  writeReg ICV_EOIR0_EL1 w__649
  let w__650 ← (( do (undefined_ID_DFR1_EL1_Type (.site 8249) ()) ) : SailM (BitVec 64) )
  writeReg ID_DFR1_EL1 w__650
  let w__651 ← (( do (undefined_bitvector_at (.site 8250) 64) ) : SailM (BitVec 64) )
  writeReg SCXTNUM_EL3 w__651
  let w__652 ← (( do (undefined_bitvector_at (.site 8251) 64) ) : SailM (BitVec 64) )
  writeReg TPIDR_EL0 w__652
  let w__653 ← (( do (undefined_bitvector_at (.site 8252) 64) ) : SailM (BitVec 64) )
  writeReg ID_AFR0_EL1 w__653
  let w__654 ← (( do (undefined_RNDRRS_Type (.site 8253) ()) ) : SailM (BitVec 64) )
  writeReg RNDRRS w__654
  let w__655 ← (( do (undefined_LORN_EL1_Type (.site 8254) ()) ) : SailM (BitVec 64) )
  writeReg LORN_EL1 w__655
  let w__656 ← (( do (undefined_ICV_IGRPEN0_EL1_Type (.site 8255) ()) ) : SailM (BitVec 64) )
  writeReg ICV_IGRPEN0_EL1 w__656
  let w__657 ← (( do (undefined_CCSIDR_EL1_Type (.site 8256) ()) ) : SailM (BitVec 64) )
  writeReg CCSIDR_EL1 w__657
  let w__658 ← (( do (undefined_SMPRIMAP_EL2_Type (.site 8257) ()) ) : SailM (BitVec 64) )
  writeReg SMPRIMAP_EL2 w__658
  let w__659 ← (( do (undefined_RNDR_Type (.site 8258) ()) ) : SailM (BitVec 64) )
  writeReg RNDR w__659
  let w__660 ← (( do (undefined_HFGRTR_EL2_Type (.site 8259) ()) ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 w__660
  let w__661 ← (( do (undefined_ID_DFR0_EL1_Type (.site 8260) ()) ) : SailM (BitVec 64) )
  writeReg ID_DFR0_EL1 w__661
  let w__662 ← (( do (undefined_ICV_IGRPEN1_EL1_Type (.site 8261) ()) ) : SailM (BitVec 64) )
  writeReg ICV_IGRPEN1_EL1 w__662
  let w__663 ← (( do (undefined_PMXEVCNTR_EL0_Type (.site 8262) ()) ) : SailM (BitVec 64) )
  writeReg PMXEVCNTR_EL0 w__663
  let w__664 ← (( do (undefined_HFGWTR2_EL2_Type (.site 8263) ()) ) : SailM (BitVec 64) )
  writeReg HFGWTR2_EL2 w__664
  let w__665 ← (( do (undefined_ICC_SGI1R_EL1_Type (.site 8264) ()) ) : SailM (BitVec 64) )
  writeReg ICC_SGI1R_EL1 w__665

def initialize_registers_13 (_ : Unit) : SailM Unit := do
  let w__666 ← (( do (undefined_bitvector_at (.site 8265) 64) ) : SailM (BitVec 64) )
  writeReg HACR_EL2 w__666
  let w__667 ← (( do (undefined_MVFR2_EL1_Type (.site 8266) ()) ) : SailM (BitVec 64) )
  writeReg MVFR2_EL1 w__667
  let w__668 ← (( do (undefined_DBGAUTHSTATUS_EL1_Type (.site 8267) ()) ) : SailM (BitVec 64) )
  writeReg DBGAUTHSTATUS_EL1 w__668
  let w__669 ← (( do (undefined_bitvector_at (.site 8268) 64) ) : SailM (BitVec 64) )
  writeReg AMAIR2_EL3 w__669
  let w__670 ← (( do (undefined_ICC_SRE_EL3_Type (.site 8269) ()) ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL3 w__670
  let w__671 ← (( do (undefined_bitvector_at (.site 8270) 64) ) : SailM (BitVec 64) )
  writeReg AFSR1_EL3 w__671
  let w__672 ← (( do (undefined_ID_MMFR3_EL1_Type (.site 8271) ()) ) : SailM (BitVec 64) )
  writeReg ID_MMFR3_EL1 w__672
  let w__673 ← (( do (undefined_HDFGWTR_EL2_Type (.site 8272) ()) ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 w__673
  let w__674 ← (( do (undefined_PMCEID1_EL0_Type (.site 8273) ()) ) : SailM (BitVec 64) )
  writeReg PMCEID1_EL0 w__674
  let w__675 ← (( do (undefined_CNTPS_TVAL_EL1_Type (.site 8274) ()) ) : SailM (BitVec 64) )
  writeReg CNTPS_TVAL_EL1 w__675
  let w__676 ← (( do (undefined_bitvector_at (.site 8275) 64) ) : SailM (BitVec 64) )
  writeReg ID_AA64AFR1_EL1 w__676
  let w__677 ← (( do (undefined_ICV_AP1R_EL1_Type (.site 8276) ()) ) : SailM (BitVec 64) )
  let w__678 ← (( do (undefined_vector 4 w__677) ) : SailM (Vector (BitVec 64) 4) )
  writeReg ICV_AP1R_EL1 w__678
  let w__679 ← (( do (undefined_LOREA_EL1_Type (.site 8277) ()) ) : SailM (BitVec 64) )
  writeReg LOREA_EL1 w__679
  let w__680 ← (( do (undefined_CNTV_TVAL_EL0_Type (.site 8278) ()) ) : SailM (BitVec 64) )
  writeReg CNTV_TVAL_EL0 w__680
  let w__681 ← (( do (undefined_ICV_DIR_EL1_Type (.site 8279) ()) ) : SailM (BitVec 64) )
  writeReg ICV_DIR_EL1 w__681
  let w__682 ← (( do (undefined_ICC_IAR1_EL1_Type (.site 8280) ()) ) : SailM (BitVec 64) )
  writeReg ICC_IAR1_EL1 w__682
  let w__683 ← (( do (undefined_MPIDR_EL1_Type (.site 8281) ()) ) : SailM (BitVec 64) )
  writeReg MPIDR_EL1 w__683
  let w__684 ← (( do (undefined_DBGCLAIMCLR_EL1_Type (.site 8282) ()) ) : SailM (BitVec 64) )
  writeReg DBGCLAIMCLR_EL1 w__684
  let w__685 ← (( do (undefined_PMCEID0_EL0_Type (.site 8283) ()) ) : SailM (BitVec 64) )
  writeReg PMCEID0_EL0 w__685
  let w__686 ← (( do (undefined_ICV_HPPIR1_EL1_Type (.site 8284) ()) ) : SailM (BitVec 64) )
  writeReg ICV_HPPIR1_EL1 w__686
  let w__687 ← (( do (undefined_bitvector_at (.site 8285) 64) ) : SailM (BitVec 64) )
  writeReg ID_AA64AFR0_EL1 w__687
  let w__688 ← (( do (undefined_bitvector_at (.site 8286) 64) ) : SailM (BitVec 64) )
  writeReg AFSR0_EL2 w__688
  let w__689 ← (( do (undefined_bitvector_at (.site 8287) 64) ) : SailM (BitVec 64) )
  writeReg AMAIR2_EL1 w__689
  let w__690 ← (( do (undefined_ID_PFR2_EL1_Type (.site 8288) ()) ) : SailM (BitVec 64) )
  writeReg ID_PFR2_EL1 w__690
  let w__691 ← (( do (undefined_SPMACCESSR_EL3_Type (.site 8289) ()) ) : SailM (BitVec 64) )
  writeReg SPMACCESSR_EL3 w__691
  let w__692 ← (( do (undefined_ICC_EOIR0_EL1_Type (.site 8290) ()) ) : SailM (BitVec 64) )
  writeReg ICC_EOIR0_EL1 w__692
  let w__693 ← (( do (undefined_ID_AA64ZFR0_EL1_Type (.site 8291) ()) ) : SailM (BitVec 64) )
  writeReg ID_AA64ZFR0_EL1 w__693
  let w__694 ← (( do (undefined_ICC_SGI1R_Type (.site 8292) ()) ) : SailM (BitVec 64) )
  writeReg _ICC_SGI1R w__694
  let w__695 ← (( do (undefined_bitvector_at (.site 8293) 64) ) : SailM (BitVec 64) )
  writeReg DBGDSAR w__695
  let w__696 ← (( do (undefined_ICC_SGI0R_Type (.site 8294) ()) ) : SailM (BitVec 64) )
  writeReg _ICC_SGI0R w__696
  let w__697 ← (( do (undefined_bitvector_at (.site 8295) 64) ) : SailM (BitVec 64) )
  writeReg _CNTVOFF w__697
  let w__698 ← (( do (undefined_ICC_ASGI1R_Type (.site 8296) ()) ) : SailM (BitVec 64) )
  writeReg _ICC_ASGI1R w__698
  let w__699 ← (( do (undefined_CNTV_CVAL_Type (.site 8297) ()) ) : SailM (BitVec 64) )
  writeReg _CNTV_CVAL w__699
  let w__700 ← (( do (undefined_DBGDRAR_Type (.site 8298) ()) ) : SailM (BitVec 64) )
  writeReg _DBGDRAR w__700
  let w__701 ← (( do (undefined_ID_AA64SMFR0_EL1_Type (.site 8299) ()) ) : SailM (BitVec 64) )
  writeReg ID_AA64SMFR0_EL1 w__701
  let w__702 ← (( do (undefined_GMID_EL1_Type (.site 8300) ()) ) : SailM (BitVec 64) )
  writeReg GMID_EL1 w__702
  let w__703 ← (( do (undefined_AMEVCNTR1_EL0_Type (.site 8301) ()) ) : SailM (BitVec 64) )
  let w__704 ← (( do (undefined_vector 16 w__703) ) : SailM (Vector (BitVec 64) 16) )
  writeReg AMEVCNTR1_EL0 w__704
  let w__705 ← (( do (undefined_bitvector_at (.site 8302) 64) ) : SailM (BitVec 64) )
  let w__706 ← (( do (undefined_vector 16 w__705) ) : SailM (Vector (BitVec 64) 16) )
  writeReg AMEVCNTVOFF0_EL2 w__706
  let w__707 ← (( do (undefined_AMEVCNTR0_Type (.site 8303) ()) ) : SailM (BitVec 64) )
  let w__708 ← (( do (undefined_vector 4 w__707) ) : SailM (Vector (BitVec 64) 4) )
  writeReg AMEVCNTR0 w__708
  let w__709 ← (( do (undefined_AMEVCNTR1_Type (.site 8304) ()) ) : SailM (BitVec 64) )
  let w__710 ← (( do (undefined_vector 16 w__709) ) : SailM (Vector (BitVec 64) 16) )
  writeReg _AMEVCNTR1 w__710
  let w__711 ← (( do (undefined_AMCR_EL0_Type (.site 8305) ()) ) : SailM (BitVec 64) )
  writeReg AMCR_EL0 w__711
  let w__712 ← (( do (undefined_AMCNTENSET0_EL0_Type (.site 8306) ()) ) : SailM (BitVec 64) )
  writeReg AMCNTENSET0_EL0 w__712
  let w__713 ← (( do (undefined_AMCNTENCLR0_EL0_Type (.site 8307) ()) ) : SailM (BitVec 64) )
  writeReg AMCNTENCLR0_EL0 w__713
  let w__714 ← (( do (undefined_AMEVTYPER0_EL0_Type (.site 8308) ()) ) : SailM (BitVec 64) )
  let w__715 ← (( do (undefined_vector 4 w__714) ) : SailM (Vector (BitVec 64) 4) )
  writeReg AMEVTYPER0_EL0 w__715
  let w__716 ← (( do (undefined_AMCNTENSET1_EL0_Type (.site 8309) ()) ) : SailM (BitVec 64) )
  writeReg AMCNTENSET1_EL0 w__716
  let w__717 ← (( do (undefined_AMCNTENCLR1_EL0_Type (.site 8310) ()) ) : SailM (BitVec 64) )
  writeReg AMCNTENCLR1_EL0 w__717
  let w__718 ← (( do (undefined_AMEVCNTR0_EL0_Type (.site 8311) ()) ) : SailM (BitVec 64) )
  let w__719 ← (( do (undefined_vector 4 w__718) ) : SailM (Vector (BitVec 64) 4) )
  writeReg _AMEVCNTR0_EL0 w__719
  let w__720 ← (( do (undefined_AMCFGR_EL0_Type (.site 8312) ()) ) : SailM (BitVec 64) )
  writeReg AMCFGR_EL0 w__720

def initialize_registers_14 (_ : Unit) : SailM Unit := do
  let w__721 ← (( do (undefined_bitvector_at (.site 8313) 64) ) : SailM (BitVec 64) )
  let w__722 ← (( do (undefined_vector 16 w__721) ) : SailM (Vector (BitVec 64) 16) )
  writeReg AMEVCNTVOFF1_EL2 w__722
  let w__723 ← (( do (undefined_AMUSERENR_EL0_Type (.site 8314) ()) ) : SailM (BitVec 64) )
  writeReg AMUSERENR_EL0 w__723
  let w__724 ← (( do (undefined_AMCG1IDR_EL0_Type (.site 8315) ()) ) : SailM (BitVec 64) )
  writeReg AMCG1IDR_EL0 w__724
  let w__725 ← (( do (undefined_AMEVTYPER1_EL0_Type (.site 8316) ()) ) : SailM (BitVec 64) )
  let w__726 ← (( do (undefined_vector 16 w__725) ) : SailM (Vector (BitVec 64) 16) )
  writeReg AMEVTYPER1_EL0 w__726
  let w__727 ← (( do (undefined_AMCGCR_EL0_Type (.site 8317) ()) ) : SailM (BitVec 64) )
  writeReg AMCGCR_EL0 w__727
  let w__728 ← (( do (undefined_bitvector_at (.site 8318) 64) ) : SailM (BitVec 64) )
  writeReg ERXADDR_EL1 w__728
  let w__729 ← (( do (undefined_bitvector_at (.site 8319) 64) ) : SailM (BitVec 64) )
  writeReg ERXMISC0_EL1 w__729
  let w__730 ← (( do (undefined_ERRIDR_EL1_Type (.site 8320) ()) ) : SailM (BitVec 64) )
  writeReg ERRIDR_EL1 w__730
  let w__731 ← (( do (undefined_bitvector_at (.site 8321) 64) ) : SailM (BitVec 64) )
  writeReg ERXPFGCDN_EL1 w__731
  let w__732 ← (( do (undefined_bitvector_at (.site 8322) 64) ) : SailM (BitVec 64) )
  writeReg ERXPFGF_EL1 w__732
  let w__733 ← (( do (undefined_ERRSELR_EL1_Type (.site 8323) ()) ) : SailM (BitVec 64) )
  writeReg ERRSELR_EL1 w__733
  let w__734 ← (( do (undefined_bitvector_at (.site 8324) 64) ) : SailM (BitVec 64) )
  writeReg ERXMISC1_EL1 w__734
  let w__735 ← (( do (undefined_bitvector_at (.site 8325) 64) ) : SailM (BitVec 64) )
  writeReg ERXCTLR_EL1 w__735
  let w__736 ← (( do (undefined_bitvector_at (.site 8326) 64) ) : SailM (BitVec 64) )
  writeReg ERXSTATUS_EL1 w__736
  let w__737 ← (( do (undefined_bitvector_at (.site 8327) 64) ) : SailM (BitVec 64) )
  writeReg ERXFR_EL1 w__737
  let w__738 ← (( do (undefined_ERXGSR_EL1_Type (.site 8328) ()) ) : SailM (BitVec 64) )
  writeReg ERXGSR_EL1 w__738
  let w__739 ← (( do (undefined_bitvector_at (.site 8329) 64) ) : SailM (BitVec 64) )
  writeReg ERXMISC3_EL1 w__739
  let w__740 ← (( do (undefined_bitvector_at (.site 8330) 64) ) : SailM (BitVec 64) )
  writeReg ERXMISC2_EL1 w__740
  let w__741 ← (( do (undefined_bitvector_at (.site 8331) 64) ) : SailM (BitVec 64) )
  writeReg ERXPFGCTL_EL1 w__741
  let w__742 ← (( do (undefined_BRBINF_EL1_Type (.site 8332) ()) ) : SailM (BitVec 64) )
  let w__743 ← (( do (undefined_vector 32 w__742) ) : SailM (Vector (BitVec 64) 32) )
  writeReg BRBINF_EL1 w__743
  let w__744 ← (( do (undefined_BRBTGT_EL1_Type (.site 8333) ()) ) : SailM (BitVec 64) )
  let w__745 ← (( do (undefined_vector 32 w__744) ) : SailM (Vector (BitVec 64) 32) )
  writeReg BRBTGT_EL1 w__745
  let w__746 ← (( do (undefined_BRBSRC_EL1_Type (.site 8334) ()) ) : SailM (BitVec 64) )
  let w__747 ← (( do (undefined_vector 32 w__746) ) : SailM (Vector (BitVec 64) 32) )
  writeReg BRBSRC_EL1 w__747
  let w__748 ← (( do (undefined_GITS_CREADR_Type (.site 8335) ()) ) : SailM (BitVec 64) )
  writeReg GITS_CREADR w__748
  let w__749 ← (( do (undefined_GICR_PENDBASER_Type (.site 8336) ()) ) : SailM (BitVec 64) )
  writeReg GICR_PENDBASER w__749
  let w__750 ← (( do (undefined_GICR_PROPBASER_Type (.site 8337) ()) ) : SailM (BitVec 64) )
  writeReg GICR_PROPBASER w__750
  let w__751 ← (( do (undefined_GICR_VPROPBASER_Type (.site 8338) ()) ) : SailM (BitVec 64) )
  writeReg GICR_VPROPBASER w__751
  let w__752 ← (( do (undefined_EDPFR_Type (.site 8339) ()) ) : SailM (BitVec 64) )
  writeReg EDPFR w__752
  let w__753 ← (( do (undefined_GICR_CLRLPIR_Type (.site 8340) ()) ) : SailM (BitVec 64) )
  writeReg GICR_CLRLPIR w__753
  let w__754 ← (( do (undefined_GICR_INVALLR_Type (.site 8341) ()) ) : SailM (BitVec 64) )
  writeReg GICR_INVALLR w__754
  let w__755 ← (( do (undefined_EDHSR_Type (.site 8342) ()) ) : SailM (BitVec 64) )
  writeReg EDHSR w__755
  let w__756 ← (( do (undefined_EDPCSR_Type (.site 8343) ()) ) : SailM (BitVec 64) )
  writeReg EDPCSR w__756
  let w__757 ← (( do (undefined_GICR_VPENDBASER_Type (.site 8344) ()) ) : SailM (BitVec 64) )
  writeReg GICR_VPENDBASER w__757
  let w__758 ← (( do (undefined_GITS_TYPER_Type (.site 8345) ()) ) : SailM (BitVec 64) )
  writeReg GITS_TYPER w__758
  let w__759 ← (( do (undefined_GITS_SGIR_Type (.site 8346) ()) ) : SailM (BitVec 64) )
  writeReg GITS_SGIR w__759
  let w__760 ← (( do (undefined_EDDFR1_Type (.site 8347) ()) ) : SailM (BitVec 64) )
  writeReg EDDFR1 w__760
  let w__761 ← (( do (undefined_GITS_CWRITER_Type (.site 8348) ()) ) : SailM (BitVec 64) )
  writeReg GITS_CWRITER w__761
  let w__762 ← (( do (undefined_EDDFR_Type (.site 8349) ()) ) : SailM (BitVec 64) )
  writeReg EDDFR w__762
  let w__763 ← (( do (undefined_GICR_INVLPIR_Type (.site 8350) ()) ) : SailM (BitVec 64) )
  writeReg GICR_INVLPIR w__763
  let w__764 ← (( do (undefined_EDAA32PFR_Type (.site 8351) ()) ) : SailM (BitVec 64) )
  writeReg EDAA32PFR w__764
  let w__765 ← (( do (undefined_GITS_CBASER_Type (.site 8352) ()) ) : SailM (BitVec 64) )
  writeReg GITS_CBASER w__765
  let w__766 ← (( do (undefined_GICR_SETLPIR_Type (.site 8353) ()) ) : SailM (BitVec 64) )
  writeReg GICR_SETLPIR w__766
  let w__767 ← (( do (undefined_PMCFGR_Type (.site 8354) ()) ) : SailM (BitVec 64) )
  writeReg PMCFGR w__767
  let w__768 ← (( do (undefined_PMCNTEN_Type (.site 8355) ()) ) : SailM (BitVec 64) )
  writeReg _PMCNTEN w__768
  let w__769 ← (( do (undefined_PMIIDR_Type (.site 8356) ()) ) : SailM (BitVec 64) )
  writeReg PMIIDR w__769
  let w__770 ← (( do (undefined_PMINTEN_Type (.site 8357) ()) ) : SailM (BitVec 64) )
  writeReg _PMINTEN w__770
  let w__771 ← (( do (undefined_PMOVS_Type (.site 8358) ()) ) : SailM (BitVec 64) )
  writeReg _PMOVS w__771
  let w__772 ← (( do (undefined_PMPCSCTL_Type (.site 8359) ()) ) : SailM (BitVec 64) )
  writeReg PMPCSCTL w__772
  let w__773 ← (( do (undefined_PMVCIDSR_Type (.site 8360) ()) ) : SailM (BitVec 64) )
  writeReg PMVCIDSR w__773

def initialize_registers_15 (_ : Unit) : SailM Unit := do
  let w__774 ← (( do (undefined_ICH_ELRSR_Type (.site 8361) ()) ) : SailM (BitVec 32) )
  writeReg _ICH_ELRSR w__774
  let w__775 ← (( do (undefined_ICC_IAR1_Type (.site 8362) ()) ) : SailM (BitVec 32) )
  writeReg _ICC_IAR1 w__775
  let w__776 ← (( do (undefined_bitvector_at (.site 8363) 32) ) : SailM (BitVec 32) )
  writeReg AIFSR_S w__776
  let w__777 ← (( do (undefined_bitvector_at (.site 8364) 32) ) : SailM (BitVec 32) )
  writeReg _AIFSR_NS w__777
  let w__778 ← (( do (undefined_ID_DFR0_Type (.site 8365) ()) ) : SailM (BitVec 32) )
  writeReg _ID_DFR0 w__778
  let w__779 ← (( do (undefined_CLIDR_Type (.site 8366) ()) ) : SailM (BitVec 32) )
  writeReg _CLIDR w__779
  let w__780 ← (( do (undefined_bitvector_at (.site 8367) 32) ) : SailM (BitVec 32) )
  writeReg _HACR w__780
  let w__781 ← (( do (undefined_bitvector_at (.site 8368) 32) ) : SailM (BitVec 32) )
  writeReg JOSCR w__781
  let w__782 ← (( do (undefined_ICV_IGRPEN1_Type (.site 8369) ()) ) : SailM (BitVec 32) )
  writeReg _ICV_IGRPEN1 w__782
  let w__783 ← (( do (undefined_CTR_Type (.site 8370) ()) ) : SailM (BitVec 32) )
  writeReg _CTR w__783
  let w__784 ← (( do (undefined_PMUSERENR_Type (.site 8371) ()) ) : SailM (BitVec 32) )
  writeReg _PMUSERENR w__784
  let w__785 ← (( do (undefined_CNTHPS_CTL_Type (.site 8372) ()) ) : SailM (BitVec 32) )
  writeReg _CNTHPS_CTL w__785
  let w__786 ← (( do (undefined_PMCEID1_Type (.site 8373) ()) ) : SailM (BitVec 32) )
  writeReg _PMCEID1 w__786
  let w__787 ← (( do (undefined_DBGAUTHSTATUS_Type (.site 8374) ()) ) : SailM (BitVec 32) )
  writeReg _DBGAUTHSTATUS w__787
  let w__788 ← (( do (undefined_ICC_IAR0_Type (.site 8375) ()) ) : SailM (BitVec 32) )
  writeReg _ICC_IAR0 w__788
  let w__789 ← (( do (undefined_ICV_IGRPEN0_Type (.site 8376) ()) ) : SailM (BitVec 32) )
  writeReg _ICV_IGRPEN0 w__789
  let w__790 ← (( do (undefined_ID_MMFR3_Type (.site 8377) ()) ) : SailM (BitVec 32) )
  writeReg _ID_MMFR3 w__790
  let w__791 ← (( do (undefined_PMCEID0_Type (.site 8378) ()) ) : SailM (BitVec 32) )
  writeReg _PMCEID0 w__791
  let w__792 ← (( do (undefined_ICV_CTLR_Type (.site 8379) ()) ) : SailM (BitVec 32) )
  writeReg _ICV_CTLR w__792
  let w__793 ← (( do (undefined_ID_ISAR6_Type (.site 8380) ()) ) : SailM (BitVec 32) )
  writeReg _ID_ISAR6 w__793
  let w__794 ← (( do (undefined_bitvector_at (.site 8381) 32) ) : SailM (BitVec 32) )
  writeReg _HACTLR w__794
  let w__795 ← (( do (undefined_DBGCLAIMCLR_Type (.site 8382) ()) ) : SailM (BitVec 32) )
  writeReg _DBGCLAIMCLR w__795
  let w__796 ← (( do (undefined_bitvector_at (.site 8383) 32) ) : SailM (BitVec 32) )
  writeReg TCMTR w__796
  let w__797 ← (( do (undefined_ICV_HPPIR1_Type (.site 8384) ()) ) : SailM (BitVec 32) )
  writeReg _ICV_HPPIR1 w__797
  let w__798 ← (( do (undefined_ID_MMFR5_Type (.site 8385) ()) ) : SailM (BitVec 32) )
  writeReg _ID_MMFR5 w__798
  let w__799 ← (( do (undefined_bitvector_at (.site 8386) 32) ) : SailM (BitVec 32) )
  let w__800 ← (( do (undefined_vector 4 w__799) ) : SailM (Vector (BitVec 32) 4) )
  writeReg _ICV_AP0R w__800
  let w__801 ← (( do (undefined_HRMR_Type (.site 8387) ()) ) : SailM (BitVec 32) )
  writeReg _HRMR w__801
  let w__802 ← (( do (undefined_ID_PFR2_Type (.site 8388) ()) ) : SailM (BitVec 32) )
  writeReg _ID_PFR2 w__802
  let w__803 ← (( do (undefined_ICV_EOIR0_Type (.site 8389) ()) ) : SailM (BitVec 32) )
  writeReg _ICV_EOIR0 w__803
  let w__804 ← (( do (undefined_ICH_VTR_Type (.site 8390) ()) ) : SailM (BitVec 32) )
  writeReg _ICH_VTR w__804
  let w__805 ← (( do (undefined_CSSELR_Type (.site 8391) ()) ) : SailM (BitVec 32) )
  writeReg CSSELR_S w__805
  let w__806 ← (( do (undefined_CSSELR_Type (.site 8392) ()) ) : SailM (BitVec 32) )
  writeReg _CSSELR_NS w__806
  let w__807 ← (( do (undefined_bitvector_at (.site 8393) 32) ) : SailM (BitVec 32) )
  writeReg JIDR w__807
  let w__808 ← (( do (undefined_ICH_VMCR_Type (.site 8394) ()) ) : SailM (BitVec 32) )
  writeReg _ICH_VMCR w__808
  let w__809 ← (( do (undefined_DBGDEVID1_Type (.site 8395) ()) ) : SailM (BitVec 32) )
  writeReg DBGDEVID1 w__809
  let w__810 ← (( do (undefined_ICC_BPR1_Type (.site 8396) ()) ) : SailM (BitVec 32) )
  writeReg _ICC_BPR1_S w__810
  let w__811 ← (( do (undefined_ICC_BPR1_Type (.site 8397) ()) ) : SailM (BitVec 32) )
  writeReg _ICC_BPR1_NS w__811
  let w__812 ← (( do (undefined_ICV_RPR_Type (.site 8398) ()) ) : SailM (BitVec 32) )
  writeReg _ICV_RPR w__812
  let w__813 ← (( do (undefined_ID_ISAR0_Type (.site 8399) ()) ) : SailM (BitVec 32) )
  writeReg _ID_ISAR0 w__813
  let w__814 ← (( do (undefined_ICV_IAR1_Type (.site 8400) ()) ) : SailM (BitVec 32) )
  writeReg _ICV_IAR1 w__814
  let w__815 ← (( do (undefined_ID_MMFR4_Type (.site 8401) ()) ) : SailM (BitVec 32) )
  writeReg _ID_MMFR4 w__815
  let w__816 ← (( do (undefined_ICC_EOIR1_Type (.site 8402) ()) ) : SailM (BitVec 32) )
  writeReg _ICC_EOIR1 w__816
  let w__817 ← (( do (undefined_bitvector_at (.site 8403) 32) ) : SailM (BitVec 32) )
  writeReg TPIDRURW_S w__817
  let w__818 ← (( do (undefined_bitvector_at (.site 8404) 32) ) : SailM (BitVec 32) )
  writeReg _TPIDRURW_NS w__818
  let w__819 ← (( do (undefined_ICC_BPR0_Type (.site 8405) ()) ) : SailM (BitVec 32) )
  writeReg _ICC_BPR0 w__819
  let w__820 ← (( do (undefined_bitvector_at (.site 8406) 32) ) : SailM (BitVec 32) )
  let w__821 ← (( do (undefined_vector 4 w__820) ) : SailM (Vector (BitVec 32) 4) )
  writeReg _ICV_AP1R w__821
  let w__822 ← (( do (undefined_bitvector_at (.site 8407) 32) ) : SailM (BitVec 32) )
  writeReg ADFSR_S w__822
  let w__823 ← (( do (undefined_bitvector_at (.site 8408) 32) ) : SailM (BitVec 32) )
  writeReg _ADFSR_NS w__823

def initialize_registers_16 (_ : Unit) : SailM Unit := do
  let w__824 ← (( do (undefined_CNTHCTL_Type (.site 8409) ()) ) : SailM (BitVec 32) )
  writeReg _CNTHCTL w__824
  let w__825 ← (( do (undefined_ICC_EOIR0_Type (.site 8410) ()) ) : SailM (BitVec 32) )
  writeReg _ICC_EOIR0 w__825
  let w__826 ← (( do (undefined_bitvector_at (.site 8411) 32) ) : SailM (BitVec 32) )
  writeReg _REVIDR w__826
  let w__827 ← (( do (undefined_ID_MMFR1_Type (.site 8412) ()) ) : SailM (BitVec 32) )
  writeReg _ID_MMFR1 w__827
  let w__828 ← (( do (undefined_ICV_BPR1_Type (.site 8413) ()) ) : SailM (BitVec 32) )
  writeReg _ICV_BPR1 w__828
  let w__829 ← (( do (undefined_ICC_RPR_Type (.site 8414) ()) ) : SailM (BitVec 32) )
  writeReg _ICC_RPR w__829
  let w__830 ← (( do (undefined_MVFR2_Type (.site 8415) ()) ) : SailM (BitVec 32) )
  writeReg _MVFR2 w__830
  let w__831 ← (( do (undefined_ICC_MSRE_Type (.site 8416) ()) ) : SailM (BitVec 32) )
  writeReg ICC_MSRE w__831
  let w__832 ← (( do (undefined_PMMIR_Type (.site 8417) ()) ) : SailM (BitVec 32) )
  writeReg PMMIR w__832
  let w__833 ← (( do (undefined_VMPIDR_Type (.site 8418) ()) ) : SailM (BitVec 32) )
  writeReg _VMPIDR w__833
  let w__834 ← (( do (undefined_ICC_IGRPEN1_Type (.site 8419) ()) ) : SailM (BitVec 32) )
  writeReg _ICC_IGRPEN1_S w__834
  let w__835 ← (( do (undefined_ICC_IGRPEN1_Type (.site 8420) ()) ) : SailM (BitVec 32) )
  writeReg _ICC_IGRPEN1_NS w__835
  let w__836 ← (( do (undefined_FPSID_Type (.site 8421) ()) ) : SailM (BitVec 32) )
  writeReg FPSID w__836
  let w__837 ← (( do (undefined_ICC_MCTLR_Type (.site 8422) ()) ) : SailM (BitVec 32) )
  writeReg ICC_MCTLR w__837
  let w__838 ← (( do (undefined_ICC_DIR_Type (.site 8423) ()) ) : SailM (BitVec 32) )
  writeReg _ICC_DIR w__838
  let w__839 ← (( do (undefined_PMSELR_Type (.site 8424) ()) ) : SailM (BitVec 32) )
  writeReg _PMSELR w__839
  let w__840 ← (( do (undefined_bitvector_at (.site 8425) 32) ) : SailM (BitVec 32) )
  writeReg _ID_AFR0 w__840
  let w__841 ← (( do (undefined_DBGCLAIMSET_Type (.site 8426) ()) ) : SailM (BitVec 32) )
  writeReg _DBGCLAIMSET w__841
  let w__842 ← (( do (undefined_bitvector_at (.site 8427) 32) ) : SailM (BitVec 32) )
  writeReg TPIDRURO_S w__842
  let w__843 ← (( do (undefined_bitvector_at (.site 8428) 32) ) : SailM (BitVec 32) )
  writeReg _TPIDRURO_NS w__843
  let w__844 ← (( do (undefined_ICC_IGRPEN0_Type (.site 8429) ()) ) : SailM (BitVec 32) )
  writeReg _ICC_IGRPEN0 w__844
  let w__845 ← (( do (undefined_DBGDTRTXext_Type (.site 8430) ()) ) : SailM (BitVec 32) )
  writeReg _DBGDTRTXext w__845
  let w__846 ← (( do (undefined_bitvector_at (.site 8431) 32) ) : SailM (BitVec 32) )
  writeReg ACTLR_S w__846
  let w__847 ← (( do (undefined_bitvector_at (.site 8432) 32) ) : SailM (BitVec 32) )
  writeReg _ACTLR_NS w__847
  let w__848 ← (( do (undefined_MVFR1_Type (.site 8433) ()) ) : SailM (BitVec 32) )
  writeReg _MVFR1 w__848
  let w__849 ← (( do (undefined_ICC_CTLR_Type (.site 8434) ()) ) : SailM (BitVec 32) )
  writeReg _ICC_CTLR_S w__849
  let w__850 ← (( do (undefined_ICC_CTLR_Type (.site 8435) ()) ) : SailM (BitVec 32) )
  writeReg _ICC_CTLR_NS w__850
  let w__851 ← (( do (undefined_DBGOSLAR_Type (.site 8436) ()) ) : SailM (BitVec 32) )
  writeReg DBGOSLAR w__851
  let w__852 ← (( do (undefined_DBGDTRRXext_Type (.site 8437) ()) ) : SailM (BitVec 32) )
  writeReg _DBGDTRRXext w__852
  let w__853 ← (( do (undefined_bitvector_at (.site 8438) 32) ) : SailM (BitVec 32) )
  let w__854 ← (( do (undefined_vector 4 w__853) ) : SailM (Vector (BitVec 32) 4) )
  writeReg _ICC_AP1R_S w__854
  let w__855 ← (( do (undefined_bitvector_at (.site 8439) 32) ) : SailM (BitVec 32) )
  let w__856 ← (( do (undefined_vector 4 w__855) ) : SailM (Vector (BitVec 32) 4) )
  writeReg _ICC_AP1R_NS w__856
  let w__857 ← (( do (undefined_CNTHVS_CTL_Type (.site 8440) ()) ) : SailM (BitVec 32) )
  writeReg _CNTHVS_CTL w__857
  let w__858 ← (( do (undefined_ICH_AP1R_Type (.site 8441) ()) ) : SailM (BitVec 32) )
  let w__859 ← (( do (undefined_vector 4 w__858) ) : SailM (Vector (BitVec 32) 4) )
  writeReg _ICH_AP1R w__859
  let w__860 ← (( do (undefined_ID_MMFR0_Type (.site 8442) ()) ) : SailM (BitVec 32) )
  writeReg _ID_MMFR0 w__860
  let w__861 ← (( do (undefined_ICV_BPR0_Type (.site 8443) ()) ) : SailM (BitVec 32) )
  writeReg _ICV_BPR0 w__861
  let w__862 ← (( do (undefined_ICH_EISR_Type (.site 8444) ()) ) : SailM (BitVec 32) )
  writeReg _ICH_EISR w__862
  let w__863 ← (( do (undefined_bitvector_at (.site 8445) 32) ) : SailM (BitVec 32) )
  writeReg AMAIR0_S w__863
  let w__864 ← (( do (undefined_bitvector_at (.site 8446) 32) ) : SailM (BitVec 32) )
  writeReg _AMAIR0_NS w__864
  let w__865 ← (( do (undefined_MVFR0_Type (.site 8447) ()) ) : SailM (BitVec 32) )
  writeReg _MVFR0 w__865
  let w__866 ← (( do (undefined_bitvector_at (.site 8448) 32) ) : SailM (BitVec 32) )
  writeReg _HAMAIR0 w__866
  let w__867 ← (( do (undefined_ICC_HSRE_Type (.site 8449) ()) ) : SailM (BitVec 32) )
  writeReg _ICC_HSRE w__867
  let w__868 ← (( do (undefined_ICH_AP0R_Type (.site 8450) ()) ) : SailM (BitVec 32) )
  let w__869 ← (( do (undefined_vector 4 w__868) ) : SailM (Vector (BitVec 32) 4) )
  writeReg _ICH_AP0R w__869
  let w__870 ← (( do (undefined_ID_ISAR5_Type (.site 8451) ()) ) : SailM (BitVec 32) )
  writeReg _ID_ISAR5 w__870
  let w__871 ← (( do (undefined_bitvector_at (.site 8452) 32) ) : SailM (BitVec 32) )
  writeReg _AIDR w__871
  let w__872 ← (( do (undefined_ICC_PMR_Type (.site 8453) ()) ) : SailM (BitVec 32) )
  writeReg _ICC_PMR w__872
  let w__873 ← (( do (undefined_ICV_EOIR1_Type (.site 8454) ()) ) : SailM (BitVec 32) )
  writeReg _ICV_EOIR1 w__873
  let w__874 ← (( do (undefined_ID_PFR1_Type (.site 8455) ()) ) : SailM (BitVec 32) )
  writeReg _ID_PFR1 w__874
  let w__875 ← (( do (undefined_ICH_HCR_Type (.site 8456) ()) ) : SailM (BitVec 32) )
  writeReg _ICH_HCR w__875

def initialize_registers_17 (_ : Unit) : SailM Unit := do
  let w__876 ← (( do (undefined_RMR_Type (.site 8457) ()) ) : SailM (BitVec 32) )
  writeReg _RMR w__876
  let w__877 ← (( do (undefined_PMCEID3_Type (.site 8458) ()) ) : SailM (BitVec 32) )
  writeReg _PMCEID3 w__877
  let w__878 ← (( do (undefined_ICC_HPPIR0_Type (.site 8459) ()) ) : SailM (BitVec 32) )
  writeReg _ICC_HPPIR0 w__878
  let w__879 ← (( do (undefined_ID_ISAR4_Type (.site 8460) ()) ) : SailM (BitVec 32) )
  writeReg _ID_ISAR4 w__879
  let w__880 ← (( do (undefined_PMCEID2_Type (.site 8461) ()) ) : SailM (BitVec 32) )
  writeReg _PMCEID2 w__880
  let w__881 ← (( do (undefined_bitvector_at (.site 8462) 32) ) : SailM (BitVec 32) )
  writeReg FCSEIDR w__881
  let w__882 ← (( do (undefined_ID_DFR1_Type (.site 8463) ()) ) : SailM (BitVec 32) )
  writeReg _ID_DFR1 w__882
  let w__883 ← (( do (undefined_ICH_LR_Type (.site 8464) ()) ) : SailM (BitVec 32) )
  let w__884 ← (( do (undefined_vector 16 w__883) ) : SailM (Vector (BitVec 32) 16) )
  writeReg _ICH_LR w__884
  let w__885 ← (( do (undefined_bitvector_at (.site 8465) 32) ) : SailM (BitVec 32) )
  writeReg _HADFSR w__885
  let w__886 ← (( do (undefined_bitvector_at (.site 8466) 32) ) : SailM (BitVec 32) )
  writeReg JMCR w__886
  let w__887 ← (( do (undefined_ICV_PMR_Type (.site 8467) ()) ) : SailM (BitVec 32) )
  writeReg _ICV_PMR w__887
  let w__888 ← (( do (undefined_ICV_HPPIR0_Type (.site 8468) ()) ) : SailM (BitVec 32) )
  writeReg _ICV_HPPIR0 w__888
  let w__889 ← (( do (undefined_bitvector_at (.site 8469) 32) ) : SailM (BitVec 32) )
  writeReg DBGWFAR w__889
  let w__890 ← (( do (undefined_ID_ISAR3_Type (.site 8470) ()) ) : SailM (BitVec 32) )
  writeReg _ID_ISAR3 w__890
  let w__891 ← (( do (undefined_ICC_MGRPEN1_Type (.site 8471) ()) ) : SailM (BitVec 32) )
  writeReg ICC_MGRPEN1 w__891
  let w__892 ← (( do (undefined_TLBTR_Type (.site 8472) ()) ) : SailM (BitVec 32) )
  writeReg TLBTR w__892
  let w__893 ← (( do (undefined_bitvector_at (.site 8473) 32) ) : SailM (BitVec 32) )
  writeReg _CNTFRQ w__893
  let w__894 ← (( do (undefined_PMINTENSET_Type (.site 8474) ()) ) : SailM (BitVec 32) )
  writeReg _PMINTENSET w__894
  let w__895 ← (( do (undefined_DBGDEVID_Type (.site 8475) ()) ) : SailM (BitVec 32) )
  writeReg DBGDEVID w__895
  let w__896 ← (( do (undefined_DBGOSECCR_Type (.site 8476) ()) ) : SailM (BitVec 32) )
  writeReg _DBGOSECCR w__896
  let w__897 ← (( do (undefined_CCSIDR2_Type (.site 8477) ()) ) : SailM (BitVec 32) )
  writeReg _CCSIDR2 w__897
  let w__898 ← (( do (undefined_CNTHV_CTL_Type (.site 8478) ()) ) : SailM (BitVec 32) )
  writeReg _CNTHV_CTL w__898
  let w__899 ← (( do (undefined_ICH_MISR_Type (.site 8479) ()) ) : SailM (BitVec 32) )
  writeReg _ICH_MISR w__899
  let w__900 ← (( do (undefined_bitvector_at (.site 8480) 32) ) : SailM (BitVec 32) )
  writeReg ACTLR2_S w__900
  let w__901 ← (( do (undefined_bitvector_at (.site 8481) 32) ) : SailM (BitVec 32) )
  writeReg _ACTLR2_NS w__901
  let w__902 ← (( do (undefined_ICV_IAR0_Type (.site 8482) ()) ) : SailM (BitVec 32) )
  writeReg _ICV_IAR0 w__902
  let w__903 ← (( do (undefined_ID_MMFR2_Type (.site 8483) ()) ) : SailM (BitVec 32) )
  writeReg _ID_MMFR2 w__903
  let w__904 ← (( do (undefined_bitvector_at (.site 8484) 32) ) : SailM (BitVec 32) )
  writeReg _HAMAIR1 w__904
  let w__905 ← (( do (undefined_ISR_Type (.site 8485) ()) ) : SailM (BitVec 32) )
  writeReg _ISR w__905
  let w__906 ← (( do (undefined_bitvector_at (.site 8486) 32) ) : SailM (BitVec 32) )
  writeReg _HAIFSR w__906
  let w__907 ← (( do (undefined_ID_PFR0_Type (.site 8487) ()) ) : SailM (BitVec 32) )
  writeReg _ID_PFR0 w__907
  let w__908 ← (( do (undefined_MIDR_Type (.site 8488) ()) ) : SailM (BitVec 32) )
  writeReg _MIDR w__908
  let w__909 ← (( do (undefined_bitvector_at (.site 8489) 32) ) : SailM (BitVec 32) )
  let w__910 ← (( do (undefined_vector 4 w__909) ) : SailM (Vector (BitVec 32) 4) )
  writeReg _ICC_AP0R w__910
  let w__911 ← (( do (undefined_DBGDIDR_Type (.site 8490) ()) ) : SailM (BitVec 32) )
  writeReg DBGDIDR w__911
  let w__912 ← (( do (undefined_bitvector_at (.site 8491) 32) ) : SailM (BitVec 32) )
  writeReg TPIDRPRW_S w__912
  let w__913 ← (( do (undefined_bitvector_at (.site 8492) 32) ) : SailM (BitVec 32) )
  writeReg _TPIDRPRW_NS w__913
  let w__914 ← (( do (undefined_DBGDTRRXint_Type (.site 8493) ()) ) : SailM (BitVec 32) )
  writeReg _DBGDTRRXint w__914
  let w__915 ← (( do (undefined_VPIDR_Type (.site 8494) ()) ) : SailM (BitVec 32) )
  writeReg _VPIDR w__915
  let w__916 ← (( do (undefined_PMSWINC_Type (.site 8495) ()) ) : SailM (BitVec 32) )
  writeReg _PMSWINC w__916
  let w__917 ← (( do (undefined_CNTV_CTL_Type (.site 8496) ()) ) : SailM (BitVec 32) )
  writeReg _CNTV_CTL w__917
  let w__918 ← (( do (undefined_bitvector_at (.site 8497) 32) ) : SailM (BitVec 32) )
  writeReg _HTPIDR w__918
  let w__919 ← (( do (undefined_ID_ISAR2_Type (.site 8498) ()) ) : SailM (BitVec 32) )
  writeReg _ID_ISAR2 w__919
  let w__920 ← (( do (undefined_DBGDTRTXint_Type (.site 8499) ()) ) : SailM (BitVec 32) )
  writeReg _DBGDTRTXint w__920
  let w__921 ← (( do (undefined_bitvector_at (.site 8500) 32) ) : SailM (BitVec 32) )
  writeReg AMAIR1_S w__921
  let w__922 ← (( do (undefined_bitvector_at (.site 8501) 32) ) : SailM (BitVec 32) )
  writeReg _AMAIR1_NS w__922
  let w__923 ← (( do (undefined_CCSIDR_Type (.site 8502) ()) ) : SailM (BitVec 32) )
  writeReg _CCSIDR w__923
  let w__924 ← (( do (undefined_bitvector_at (.site 8503) 32) ) : SailM (BitVec 32) )
  writeReg DBGDEVID2 w__924
  let w__925 ← (( do (undefined_ICV_DIR_Type (.site 8504) ()) ) : SailM (BitVec 32) )
  writeReg _ICV_DIR w__925

def initialize_registers_18 (_ : Unit) : SailM Unit := do
  let w__926 ← (( do (undefined_MPIDR_Type (.site 8505) ()) ) : SailM (BitVec 32) )
  writeReg _MPIDR w__926
  let w__927 ← (( do (undefined_ICH_LRC_Type (.site 8506) ()) ) : SailM (BitVec 32) )
  let w__928 ← (( do (undefined_vector 16 w__927) ) : SailM (Vector (BitVec 32) 16) )
  writeReg _ICH_LRC w__928
  let w__929 ← (( do (undefined_ICC_HPPIR1_Type (.site 8507) ()) ) : SailM (BitVec 32) )
  writeReg _ICC_HPPIR1 w__929
  let w__930 ← (( do (undefined_ICC_SRE_Type (.site 8508) ()) ) : SailM (BitVec 32) )
  writeReg _ICC_SRE_S w__930
  let w__931 ← (( do (undefined_ICC_SRE_Type (.site 8509) ()) ) : SailM (BitVec 32) )
  writeReg _ICC_SRE_NS w__931
  let w__932 ← (( do (undefined_ID_ISAR1_Type (.site 8510) ()) ) : SailM (BitVec 32) )
  writeReg _ID_ISAR1 w__932
  let w__933 ← (( do (undefined_AMEVTYPER0_Type (.site 8511) ()) ) : SailM (BitVec 32) )
  let w__934 ← (( do (undefined_vector 4 w__933) ) : SailM (Vector (BitVec 32) 4) )
  writeReg _AMEVTYPER0 w__934
  let w__935 ← (( do (undefined_AMUSERENR_Type (.site 8512) ()) ) : SailM (BitVec 32) )
  writeReg _AMUSERENR w__935
  let w__936 ← (( do (undefined_AMEVTYPER1_Type (.site 8513) ()) ) : SailM (BitVec 32) )
  let w__937 ← (( do (undefined_vector 16 w__936) ) : SailM (Vector (BitVec 32) 16) )
  writeReg _AMEVTYPER1 w__937
  let w__938 ← (( do (undefined_AMCGCR_Type (.site 8514) ()) ) : SailM (BitVec 32) )
  writeReg _AMCGCR w__938
  let w__939 ← (( do (undefined_AMCFGR_Type (.site 8515) ()) ) : SailM (BitVec 32) )
  writeReg _AMCFGR w__939
  let w__940 ← (( do (undefined_AMCNTENCLR1_Type (.site 8516) ()) ) : SailM (BitVec 32) )
  writeReg _AMCNTENCLR1 w__940
  let w__941 ← (( do (undefined_AMCNTENSET0_Type (.site 8517) ()) ) : SailM (BitVec 32) )
  writeReg _AMCNTENSET0 w__941
  let w__942 ← (( do (undefined_AMCNTENCLR0_Type (.site 8518) ()) ) : SailM (BitVec 32) )
  writeReg _AMCNTENCLR0 w__942
  let w__943 ← (( do (undefined_AMCNTENSET1_Type (.site 8519) ()) ) : SailM (BitVec 32) )
  writeReg _AMCNTENSET1 w__943
  let w__944 ← (( do (undefined_AMCR_Type (.site 8520) ()) ) : SailM (BitVec 32) )
  writeReg _AMCR w__944
  let w__945 ← (( do (undefined_ERRIDR_Type (.site 8521) ()) ) : SailM (BitVec 32) )
  writeReg _ERRIDR w__945
  let w__946 ← (( do (undefined_bitvector_at (.site 8522) 32) ) : SailM (BitVec 32) )
  writeReg _ERXFR2 w__946
  let w__947 ← (( do (undefined_bitvector_at (.site 8523) 32) ) : SailM (BitVec 32) )
  writeReg _ERXMISC2 w__947
  let w__948 ← (( do (undefined_bitvector_at (.site 8524) 32) ) : SailM (BitVec 32) )
  writeReg _ERXFR w__948
  let w__949 ← (( do (undefined_bitvector_at (.site 8525) 32) ) : SailM (BitVec 32) )
  writeReg _ERXADDR w__949
  let w__950 ← (( do (undefined_bitvector_at (.site 8526) 32) ) : SailM (BitVec 32) )
  writeReg _ERXMISC0 w__950
  let w__951 ← (( do (undefined_bitvector_at (.site 8527) 32) ) : SailM (BitVec 32) )
  writeReg _ERXMISC5 w__951
  let w__952 ← (( do (undefined_ERRSELR_Type (.site 8528) ()) ) : SailM (BitVec 32) )
  writeReg _ERRSELR w__952
  let w__953 ← (( do (undefined_bitvector_at (.site 8529) 32) ) : SailM (BitVec 32) )
  writeReg _ERXCTLR2 w__953
  let w__954 ← (( do (undefined_bitvector_at (.site 8530) 32) ) : SailM (BitVec 32) )
  writeReg _ERXMISC1 w__954
  let w__955 ← (( do (undefined_bitvector_at (.site 8531) 32) ) : SailM (BitVec 32) )
  writeReg _ERXCTLR w__955
  let w__956 ← (( do (undefined_bitvector_at (.site 8532) 32) ) : SailM (BitVec 32) )
  writeReg _ERXMISC6 w__956
  let w__957 ← (( do (undefined_bitvector_at (.site 8533) 32) ) : SailM (BitVec 32) )
  writeReg _ERXMISC4 w__957
  let w__958 ← (( do (undefined_bitvector_at (.site 8534) 32) ) : SailM (BitVec 32) )
  writeReg _ERXADDR2 w__958
  let w__959 ← (( do (undefined_bitvector_at (.site 8535) 32) ) : SailM (BitVec 32) )
  writeReg _ERXMISC7 w__959
  let w__960 ← (( do (undefined_bitvector_at (.site 8536) 32) ) : SailM (BitVec 32) )
  writeReg _ERXMISC3 w__960
  let w__961 ← (( do (undefined_bitvector_at (.site 8537) 32) ) : SailM (BitVec 32) )
  writeReg _ERXSTATUS w__961
  let w__962 ← (( do (undefined_GICD_CTLR_Type (.site 8538) ()) ) : SailM (BitVec 32) )
  writeReg GICD_CTLR w__962
  let w__963 ← (( do (undefined_GICC_IAR_Type (.site 8539) ()) ) : SailM (BitVec 32) )
  writeReg GICC_IAR w__963
  let w__964 ← (( do (undefined_CTILAR_Type (.site 8540) ()) ) : SailM (BitVec 32) )
  writeReg CTILAR w__964
  let w__965 ← (( do (undefined_CTIPIDR2_Type (.site 8541) ()) ) : SailM (BitVec 32) )
  writeReg CTIPIDR2 w__965
  let w__966 ← (( do (undefined_CTICIDR1_Type (.site 8542) ()) ) : SailM (BitVec 32) )
  writeReg CTICIDR1 w__966
  let w__967 ← (( do (undefined_GICH_MISR_Type (.site 8543) ()) ) : SailM (BitVec 32) )
  writeReg GICH_MISR w__967
  let w__968 ← (( do (undefined_CTIDEVTYPE_Type (.site 8544) ()) ) : SailM (BitVec 32) )
  writeReg CTIDEVTYPE w__968
  let w__969 ← (( do (undefined_GITS_CTLR_Type (.site 8545) ()) ) : SailM (BitVec 32) )
  writeReg GITS_CTLR w__969
  let w__970 ← (( do (undefined_GICR_IIDR_Type (.site 8546) ()) ) : SailM (BitVec 32) )
  writeReg GICR_IIDR w__970
  let w__971 ← (( do (undefined_EDDEVARCH_Type (.site 8547) ()) ) : SailM (BitVec 32) )
  writeReg EDDEVARCH w__971
  let w__972 ← (( do (undefined_CTIPIDR1_Type (.site 8548) ()) ) : SailM (BitVec 32) )
  writeReg CTIPIDR1 w__972
  let w__973 ← (( do (undefined_GICV_IAR_Type (.site 8549) ()) ) : SailM (BitVec 32) )
  writeReg GICV_IAR w__973
  let w__974 ← (( do (undefined_CNTSR_Type (.site 8550) ()) ) : SailM (BitVec 32) )
  writeReg CNTSR w__974
  let w__975 ← (( do (undefined_EDCIDR3_Type (.site 8551) ()) ) : SailM (BitVec 32) )
  writeReg EDCIDR3 w__975
  let w__976 ← (( do (undefined_GICM_SETSPI_NSR_Type (.site 8552) ()) ) : SailM (BitVec 32) )
  writeReg GICM_SETSPI_NSR w__976

def initialize_registers_19 (_ : Unit) : SailM Unit := do
  let w__977 ← (( do (undefined_GICR_WAKER_Type (.site 8553) ()) ) : SailM (BitVec 32) )
  writeReg GICR_WAKER w__977
  let w__978 ← (( do (undefined_GITS_PARTIDR_Type (.site 8554) ()) ) : SailM (BitVec 32) )
  writeReg GITS_PARTIDR w__978
  let w__979 ← (( do (undefined_GICV_HPPIR_Type (.site 8555) ()) ) : SailM (BitVec 32) )
  writeReg GICV_HPPIR w__979
  let w__980 ← (( do (undefined_CTIPIDR0_Type (.site 8556) ()) ) : SailM (BitVec 32) )
  writeReg CTIPIDR0 w__980
  let w__981 ← (( do (undefined_GICM_SETSPI_SR_Type (.site 8557) ()) ) : SailM (BitVec 32) )
  writeReg GICM_SETSPI_SR w__981
  let w__982 ← (( do (undefined_GICV_DIR_Type (.site 8558) ()) ) : SailM (BitVec 32) )
  writeReg GICV_DIR w__982
  let w__983 ← (( do (undefined_bitvector_at (.site 8559) 32) ) : SailM (BitVec 32) )
  writeReg CTIDEVID2 w__983
  let w__984 ← (( do (undefined_EDPIDR3_Type (.site 8560) ()) ) : SailM (BitVec 32) )
  writeReg EDPIDR3 w__984
  let w__985 ← (( do (undefined_GICC_STATUSR_Type (.site 8561) ()) ) : SailM (BitVec 32) )
  writeReg GICC_STATUSR w__985
  let w__986 ← (( do (undefined_GICM_IIDR_Type (.site 8562) ()) ) : SailM (BitVec 32) )
  writeReg GICM_IIDR w__986
  let w__987 ← (( do (undefined_GICR_VSGIR_Type (.site 8563) ()) ) : SailM (BitVec 32) )
  writeReg GICR_VSGIR w__987
  let w__988 ← (( do (undefined_EDDEVTYPE_Type (.site 8564) ()) ) : SailM (BitVec 32) )
  writeReg EDDEVTYPE w__988
  let w__989 ← (( do (undefined_GICM_TYPER_Type (.site 8565) ()) ) : SailM (BitVec 32) )
  writeReg GICM_TYPER w__989
  let w__990 ← (( do (undefined_GICD_TYPER2_Type (.site 8566) ()) ) : SailM (BitVec 32) )
  writeReg GICD_TYPER2 w__990
  let w__991 ← (( do (undefined_GICH_EISR_Type (.site 8567) ()) ) : SailM (BitVec 32) )
  writeReg GICH_EISR w__991
  let w__992 ← (( do (undefined_GICH_ELRSR_Type (.site 8568) ()) ) : SailM (BitVec 32) )
  writeReg GICH_ELRSR w__992
  let w__993 ← (( do (undefined_GICM_CLRSPI_NSR_Type (.site 8569) ()) ) : SailM (BitVec 32) )
  writeReg GICM_CLRSPI_NSR w__993
  let w__994 ← (( do (undefined_GICV_STATUSR_Type (.site 8570) ()) ) : SailM (BitVec 32) )
  writeReg GICV_STATUSR w__994
  let w__995 ← (( do (undefined_EDPIDR1_Type (.site 8571) ()) ) : SailM (BitVec 32) )
  writeReg EDPIDR1 w__995
  let w__996 ← (( do (undefined_GICM_CLRSPI_SR_Type (.site 8572) ()) ) : SailM (BitVec 32) )
  writeReg GICM_CLRSPI_SR w__996
  let w__997 ← (( do (undefined_GICV_AEOIR_Type (.site 8573) ()) ) : SailM (BitVec 32) )
  writeReg GICV_AEOIR w__997
  let w__998 ← (( do (undefined_GICC_PMR_Type (.site 8574) ()) ) : SailM (BitVec 32) )
  writeReg GICC_PMR w__998
  let w__999 ← (( do (undefined_GICV_ABPR_Type (.site 8575) ()) ) : SailM (BitVec 32) )
  writeReg GICV_ABPR w__999
  let w__1000 ← (( do (undefined_CTIDEVARCH_Type (.site 8576) ()) ) : SailM (BitVec 32) )
  writeReg CTIDEVARCH w__1000
  let w__1001 ← (( do (undefined_GICR_MPAMIDR_Type (.site 8577) ()) ) : SailM (BitVec 32) )
  writeReg GICR_MPAMIDR w__1001
  let w__1002 ← (( do (undefined_CTICIDR3_Type (.site 8578) ()) ) : SailM (BitVec 32) )
  writeReg CTICIDR3 w__1002
  let w__1003 ← (( do (undefined_GICC_RPR_Type (.site 8579) ()) ) : SailM (BitVec 32) )
  writeReg GICC_RPR w__1003
  let w__1004 ← (( do (undefined_GICV_AIAR_Type (.site 8580) ()) ) : SailM (BitVec 32) )
  writeReg GICV_AIAR w__1004
  let w__1005 ← (( do (undefined_GICV_RPR_Type (.site 8581) ()) ) : SailM (BitVec 32) )
  writeReg GICV_RPR w__1005
  let w__1006 ← (( do (undefined_GICV_AHPPIR_Type (.site 8582) ()) ) : SailM (BitVec 32) )
  writeReg GICV_AHPPIR w__1006
  let w__1007 ← (( do (undefined_GICR_CTLR_Type (.site 8583) ()) ) : SailM (BitVec 32) )
  writeReg GICR_CTLR w__1007
  let w__1008 ← (( do (undefined_CNTEL0ACR_Type (.site 8584) ()) ) : SailM (BitVec 32) )
  writeReg CNTEL0ACR w__1008
  let w__1009 ← (( do (undefined_GICV_BPR_Type (.site 8585) ()) ) : SailM (BitVec 32) )
  writeReg GICV_BPR w__1009
  let w__1010 ← (( do (undefined_bitvector_at (.site 8586) 32) ) : SailM (BitVec 32) )
  writeReg EDDEVID2 w__1010
  let w__1011 ← (( do (undefined_GICV_EOIR_Type (.site 8587) ()) ) : SailM (BitVec 32) )
  writeReg GICV_EOIR w__1011
  let w__1012 ← (( do (undefined_CNTFID0_Type (.site 8588) ()) ) : SailM (BitVec 32) )
  writeReg CNTFID0 w__1012
  let w__1013 ← (( do (undefined_GICD_TYPER_Type (.site 8589) ()) ) : SailM (BitVec 32) )
  writeReg GICD_TYPER w__1013
  let w__1014 ← (( do (undefined_CTICIDR0_Type (.site 8590) ()) ) : SailM (BitVec 32) )
  writeReg CTICIDR0 w__1014
  let w__1015 ← (( do (undefined_GICC_HPPIR_Type (.site 8591) ()) ) : SailM (BitVec 32) )
  writeReg GICC_HPPIR w__1015
  let w__1016 ← (( do (undefined_GICD_CLRSPI_NSR_Type (.site 8592) ()) ) : SailM (BitVec 32) )
  writeReg GICD_CLRSPI_NSR w__1016
  let w__1017 ← (( do (undefined_CTIITCTRL_Type (.site 8593) ()) ) : SailM (BitVec 32) )
  writeReg CTIITCTRL w__1017
  let w__1018 ← (( do (undefined_GITS_STATUSR_Type (.site 8594) ()) ) : SailM (BitVec 32) )
  writeReg GITS_STATUSR w__1018
  let w__1019 ← (( do (undefined_GICH_VTR_Type (.site 8595) ()) ) : SailM (BitVec 32) )
  writeReg GICH_VTR w__1019
  let w__1020 ← (( do (undefined_CTIPIDR3_Type (.site 8596) ()) ) : SailM (BitVec 32) )
  writeReg CTIPIDR3 w__1020
  let w__1021 ← (( do (undefined_GICC_CTLR_Type (.site 8597) ()) ) : SailM (BitVec 32) )
  writeReg GICC_CTLR w__1021
  let w__1022 ← (( do (undefined_EDPIDR4_Type (.site 8598) ()) ) : SailM (BitVec 32) )
  writeReg EDPIDR4 w__1022
  let w__1023 ← (( do (undefined_CTICONTROL_Type (.site 8599) ()) ) : SailM (BitVec 32) )
  writeReg CTICONTROL w__1023
  let w__1024 ← (( do (undefined_GICR_INMIR0_Type (.site 8600) ()) ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 w__1024

def initialize_registers_20 (_ : Unit) : SailM Unit := do
  let w__1025 ← (( do (undefined_GICD_CLRSPI_SR_Type (.site 8601) ()) ) : SailM (BitVec 32) )
  writeReg GICD_CLRSPI_SR w__1025
  let w__1026 ← (( do (undefined_GICV_CTLR_Type (.site 8602) ()) ) : SailM (BitVec 32) )
  writeReg GICV_CTLR w__1026
  let w__1027 ← (( do (undefined_GICR_PARTIDR_Type (.site 8603) ()) ) : SailM (BitVec 32) )
  writeReg GICR_PARTIDR w__1027
  let w__1028 ← (( do (undefined_EDDEVID1_Type (.site 8604) ()) ) : SailM (BitVec 32) )
  writeReg EDDEVID1 w__1028
  let w__1029 ← (( do (undefined_EDPRCR_Type (.site 8605) ()) ) : SailM (BitVec 32) )
  writeReg EDPRCR w__1029
  let w__1030 ← (( do (undefined_GICR_VSGIPENDR_Type (.site 8606) ()) ) : SailM (BitVec 32) )
  writeReg GICR_VSGIPENDR w__1030
  let w__1031 ← (( do (undefined_GICD_STATUSR_Type (.site 8607) ()) ) : SailM (BitVec 32) )
  writeReg GICD_STATUSR w__1031
  let w__1032 ← (( do (undefined_GICR_ISENABLER0_Type (.site 8608) ()) ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 w__1032
  let w__1033 ← (( do (undefined_CTICIDR2_Type (.site 8609) ()) ) : SailM (BitVec 32) )
  writeReg CTICIDR2 w__1033
  let w__1034 ← (( do (undefined_EDRCR_Type (.site 8610) ()) ) : SailM (BitVec 32) )
  writeReg EDRCR w__1034
  let w__1035 ← (( do (undefined_GICV_PMR_Type (.site 8611) ()) ) : SailM (BitVec 32) )
  writeReg GICV_PMR w__1035
  let w__1036 ← (( do (undefined_EDDEVID_Type (.site 8612) ()) ) : SailM (BitVec 32) )
  writeReg EDDEVID w__1036
  let w__1037 ← (( do (undefined_GICC_DIR_Type (.site 8613) ()) ) : SailM (BitVec 32) )
  writeReg GICC_DIR w__1037
  let w__1038 ← (( do (undefined_EDCIDR0_Type (.site 8614) ()) ) : SailM (BitVec 32) )
  writeReg EDCIDR0 w__1038
  let w__1039 ← (( do (undefined_GITS_MPAMIDR_Type (.site 8615) ()) ) : SailM (BitVec 32) )
  writeReg GITS_MPAMIDR w__1039
  let w__1040 ← (( do (undefined_GICD_SGIR_Type (.site 8616) ()) ) : SailM (BitVec 32) )
  writeReg GICD_SGIR w__1040
  let w__1041 ← (( do (undefined_GICH_VMCR_Type (.site 8617) ()) ) : SailM (BitVec 32) )
  writeReg GICH_VMCR w__1041
  let w__1042 ← (( do (undefined_EDLAR_Type (.site 8618) ()) ) : SailM (BitVec 32) )
  writeReg EDLAR w__1042
  let w__1043 ← (( do (undefined_GICC_AEOIR_Type (.site 8619) ()) ) : SailM (BitVec 32) )
  writeReg GICC_AEOIR w__1043
  let w__1044 ← (( do (undefined_GICC_AHPPIR_Type (.site 8620) ()) ) : SailM (BitVec 32) )
  writeReg GICC_AHPPIR w__1044
  let w__1045 ← (( do (undefined_GICR_SYNCR_Type (.site 8621) ()) ) : SailM (BitVec 32) )
  writeReg GICR_SYNCR w__1045
  let w__1046 ← (( do (undefined_GICC_ABPR_Type (.site 8622) ()) ) : SailM (BitVec 32) )
  writeReg GICC_ABPR w__1046
  let w__1047 ← (( do (undefined_CTIPIDR4_Type (.site 8623) ()) ) : SailM (BitVec 32) )
  writeReg CTIPIDR4 w__1047
  let w__1048 ← (( do (undefined_bitvector_at (.site 8624) 32) ) : SailM (BitVec 32) )
  writeReg CTIDEVID1 w__1048
  let w__1049 ← (( do (undefined_GITS_MPIDR_Type (.site 8625) ()) ) : SailM (BitVec 32) )
  writeReg GITS_MPIDR w__1049
  let w__1050 ← (( do (undefined_EDCIDR2_Type (.site 8626) ()) ) : SailM (BitVec 32) )
  writeReg EDCIDR2 w__1050
  let w__1051 ← (( do (undefined_GICD_SETSPI_NSR_Type (.site 8627) ()) ) : SailM (BitVec 32) )
  writeReg GICD_SETSPI_NSR w__1051
  let w__1052 ← (( do (undefined_CNTID_Type (.site 8628) ()) ) : SailM (BitVec 32) )
  writeReg CNTID w__1052
  let w__1053 ← (( do (undefined_GITS_IIDR_Type (.site 8629) ()) ) : SailM (BitVec 32) )
  writeReg GITS_IIDR w__1053
  let w__1054 ← (( do (undefined_EDPIDR0_Type (.site 8630) ()) ) : SailM (BitVec 32) )
  writeReg EDPIDR0 w__1054
  let w__1055 ← (( do (undefined_CTIAUTHSTATUS_Type (.site 8631) ()) ) : SailM (BitVec 32) )
  writeReg CTIAUTHSTATUS w__1055
  let w__1056 ← (( do (undefined_GICH_HCR_Type (.site 8632) ()) ) : SailM (BitVec 32) )
  writeReg GICH_HCR w__1056
  let w__1057 ← (( do (undefined_GICC_BPR_Type (.site 8633) ()) ) : SailM (BitVec 32) )
  writeReg GICC_BPR w__1057
  let w__1058 ← (( do (undefined_CTIDEVID_Type (.site 8634) ()) ) : SailM (BitVec 32) )
  writeReg CTIDEVID w__1058
  let w__1059 ← (( do (undefined_GICD_SETSPI_SR_Type (.site 8635) ()) ) : SailM (BitVec 32) )
  writeReg GICD_SETSPI_SR w__1059
  let w__1060 ← (( do (undefined_GICR_STATUSR_Type (.site 8636) ()) ) : SailM (BitVec 32) )
  writeReg GICR_STATUSR w__1060
  let w__1061 ← (( do (undefined_GICC_EOIR_Type (.site 8637) ()) ) : SailM (BitVec 32) )
  writeReg GICC_EOIR w__1061
  let w__1062 ← (( do (undefined_EDPIDR2_Type (.site 8638) ()) ) : SailM (BitVec 32) )
  writeReg EDPIDR2 w__1062
  let w__1063 ← (( do (undefined_CNTNSAR_Type (.site 8639) ()) ) : SailM (BitVec 32) )
  writeReg CNTNSAR w__1063
  let w__1064 ← (( do (undefined_EDITCTRL_Type (.site 8640) ()) ) : SailM (BitVec 32) )
  writeReg EDITCTRL w__1064
  let w__1065 ← (( do (undefined_GICD_IIDR_Type (.site 8641) ()) ) : SailM (BitVec 32) )
  writeReg GICD_IIDR w__1065
  let w__1066 ← (( do (undefined_EDCIDR1_Type (.site 8642) ()) ) : SailM (BitVec 32) )
  writeReg EDCIDR1 w__1066
  let w__1067 ← (( do (undefined_GICC_AIAR_Type (.site 8643) ()) ) : SailM (BitVec 32) )
  writeReg GICC_AIAR w__1067
  let w__1068 ← (( do (undefined_AMPIDR2_Type (.site 8644) ()) ) : SailM (BitVec 32) )
  writeReg AMPIDR2 w__1068
  let w__1069 ← (( do (undefined_AMPIDR4_Type (.site 8645) ()) ) : SailM (BitVec 32) )
  writeReg AMPIDR4 w__1069
  let w__1070 ← (( do (undefined_AMIIDR_Type (.site 8646) ()) ) : SailM (BitVec 32) )
  writeReg AMIIDR w__1070
  let w__1071 ← (( do (undefined_AMPIDR3_Type (.site 8647) ()) ) : SailM (BitVec 32) )
  writeReg AMPIDR3 w__1071
  let w__1072 ← (( do (undefined_AMCIDR3_Type (.site 8648) ()) ) : SailM (BitVec 32) )
  writeReg AMCIDR3 w__1072

def initialize_registers_21 (_ : Unit) : SailM Unit := do
  let w__1073 ← (( do (undefined_AMDEVARCH_Type (.site 8649) ()) ) : SailM (BitVec 32) )
  writeReg AMDEVARCH w__1073
  let w__1074 ← (( do (undefined_AMPIDR0_Type (.site 8650) ()) ) : SailM (BitVec 32) )
  writeReg AMPIDR0 w__1074
  let w__1075 ← (( do (undefined_AMCIDR2_Type (.site 8651) ()) ) : SailM (BitVec 32) )
  writeReg AMCIDR2 w__1075
  let w__1076 ← (( do (undefined_AMCIDR0_Type (.site 8652) ()) ) : SailM (BitVec 32) )
  writeReg AMCIDR0 w__1076
  let w__1077 ← (( do (undefined_AMPIDR1_Type (.site 8653) ()) ) : SailM (BitVec 32) )
  writeReg AMPIDR1 w__1077
  let w__1078 ← (( do (undefined_AMCIDR1_Type (.site 8654) ()) ) : SailM (BitVec 32) )
  writeReg AMCIDR1 w__1078
  let w__1079 ← (( do (undefined_AMDEVTYPE_Type (.site 8655) ()) ) : SailM (BitVec 32) )
  writeReg AMDEVTYPE w__1079
  let w__1080 ← (( do (undefined_bitvector_at (.site 8656) 32) ) : SailM (BitVec 32) )
  writeReg _HACTLR2 w__1080
  let w__1081 ← (( do (undefined_PMAUTHSTATUS_Type (.site 8657) ()) ) : SailM (BitVec 32) )
  writeReg PMAUTHSTATUS w__1081
  let w__1082 ← (( do (undefined_PMCGCR0_Type (.site 8658) ()) ) : SailM (BitVec 32) )
  writeReg PMCGCR0 w__1082
  let w__1083 ← (( do (undefined_PMCIDR0_Type (.site 8659) ()) ) : SailM (BitVec 32) )
  writeReg PMCIDR0 w__1083
  let w__1084 ← (( do (undefined_PMCIDR1_Type (.site 8660) ()) ) : SailM (BitVec 32) )
  writeReg PMCIDR1 w__1084
  let w__1085 ← (( do (undefined_PMCIDR2_Type (.site 8661) ()) ) : SailM (BitVec 32) )
  writeReg PMCIDR2 w__1085
  let w__1086 ← (( do (undefined_PMCIDR3_Type (.site 8662) ()) ) : SailM (BitVec 32) )
  writeReg PMCIDR3 w__1086
  let w__1087 ← (( do (undefined_PMDEVID_Type (.site 8663) ()) ) : SailM (BitVec 32) )
  writeReg PMDEVID w__1087
  let w__1088 ← (( do (undefined_PMDEVTYPE_Type (.site 8664) ()) ) : SailM (BitVec 32) )
  writeReg PMDEVTYPE w__1088
  let w__1089 ← (( do (undefined_PMITCTRL_Type (.site 8665) ()) ) : SailM (BitVec 32) )
  writeReg PMITCTRL w__1089
  let w__1090 ← (( do (undefined_PMLAR_Type (.site 8666) ()) ) : SailM (BitVec 32) )
  writeReg PMLAR w__1090
  let w__1091 ← (( do (undefined_PMPIDR0_Type (.site 8667) ()) ) : SailM (BitVec 32) )
  writeReg PMPIDR0 w__1091
  let w__1092 ← (( do (undefined_PMPIDR1_Type (.site 8668) ()) ) : SailM (BitVec 32) )
  writeReg PMPIDR1 w__1092
  let w__1093 ← (( do (undefined_PMPIDR2_Type (.site 8669) ()) ) : SailM (BitVec 32) )
  writeReg PMPIDR2 w__1093
  let w__1094 ← (( do (undefined_PMPIDR3_Type (.site 8670) ()) ) : SailM (BitVec 32) )
  writeReg PMPIDR3 w__1094
  let w__1095 ← (( do (undefined_PMPIDR4_Type (.site 8671) ()) ) : SailM (BitVec 32) )
  writeReg PMPIDR4 w__1095

def initialize_registers (_ : Unit) : SailM Unit := do
  initialize_registers_0 ()
  initialize_registers_1 ()
  initialize_registers_2 ()
  initialize_registers_3 ()
  initialize_registers_4 ()
  initialize_registers_5 ()
  initialize_registers_6 ()
  initialize_registers_7 ()
  initialize_registers_8 ()
  initialize_registers_9 ()
  initialize_registers_10 ()
  initialize_registers_11 ()
  initialize_registers_12 ()
  initialize_registers_13 ()
  initialize_registers_14 ()
  initialize_registers_15 ()
  initialize_registers_16 ()
  initialize_registers_17 ()
  initialize_registers_18 ()
  initialize_registers_19 ()
  initialize_registers_20 ()
  initialize_registers_21 ()


end ArmFull.Functions
