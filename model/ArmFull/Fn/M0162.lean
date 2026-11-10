import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0036
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0048
import ArmFull.Fn.M0049
import ArmFull.Fn.M0058
import ArmFull.Fn.M0073
import ArmFull.Fn.M0079
import ArmFull.Fn.M0080
import ArmFull.Fn.M0100
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146

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
def AMCNTENCLR0_EL0_SysRegWrite_87e21241643a862e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((IsHighestEL w__0.EL) : Bool)
  then
    (do
      let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg AMCNTENCLR0_EL0 (Mk_AMCNTENCLR0_EL0_Type w__1))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMCNTENCLR1_EL0_SysRegWrite_c63fb61a666d3a21 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((IsHighestEL w__0.EL) : Bool)
  then
    (do
      let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg AMCNTENCLR1_EL0 (Mk_AMCNTENCLR1_EL0_Type w__1))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMCNTENSET0_EL0_SysRegWrite_b4e12b5dd3b0738a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((IsHighestEL w__0.EL) : Bool)
  then
    (do
      let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg AMCNTENSET0_EL0 (Mk_AMCNTENSET0_EL0_Type w__1))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMCNTENSET1_EL0_SysRegWrite_a3bee0219e2d4b9e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((IsHighestEL w__0.EL) : Bool)
  then
    (do
      let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg AMCNTENSET1_EL0 (Mk_AMCNTENSET1_EL0_Type w__1))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMCR_EL0_SysRegWrite_6a9019dd97aa8af1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((IsHighestEL w__0.EL) : Bool)
  then
    (do
      let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg AMCR_EL0 (Mk_AMCR_EL0_Type w__1))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMEVCNTR0_EL0_SysRegWrite_57776cdcd88bec7e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((IsHighestEL w__0.EL) : Bool)
  then
    (do
      let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      (AMEVCNTR0_EL0_set 2 (Mk_AMEVCNTR0_EL0_Type w__1)))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMEVCNTR0_EL0_SysRegWrite_a28bd21dde7b55b6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((IsHighestEL w__0.EL) : Bool)
  then
    (do
      let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      (AMEVCNTR0_EL0_set 1 (Mk_AMEVCNTR0_EL0_Type w__1)))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMEVCNTR0_EL0_SysRegWrite_ca5a4224a458ea03 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((IsHighestEL w__0.EL) : Bool)
  then
    (do
      let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      (AMEVCNTR0_EL0_set 0 (Mk_AMEVCNTR0_EL0_Type w__1)))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMEVCNTR0_EL0_SysRegWrite_df6bb2663cab03ed (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((IsHighestEL w__0.EL) : Bool)
  then
    (do
      let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      (AMEVCNTR0_EL0_set 3 (Mk_AMEVCNTR0_EL0_Type w__1)))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_2bb86c4004ef9258 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 0) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__1.EL) : Bool)
      then
        (do
          let w__2 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__2 0 (Mk_AMEVCNTR1_EL0_Type w__3)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_2cb2cddc132a8d44 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 6) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__1.EL) : Bool)
      then
        (do
          let w__2 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__2 6 (Mk_AMEVCNTR1_EL0_Type w__3)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_3743486d55da4508 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 1) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__1.EL) : Bool)
      then
        (do
          let w__2 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__2 1 (Mk_AMEVCNTR1_EL0_Type w__3)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_44cf3260f4372341 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 5) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__1.EL) : Bool)
      then
        (do
          let w__2 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__2 5 (Mk_AMEVCNTR1_EL0_Type w__3)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_4a152435dd65137a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 10) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__1.EL) : Bool)
      then
        (do
          let w__2 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__2 10 (Mk_AMEVCNTR1_EL0_Type w__3)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_5139d9a03c76c81b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 3) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__1.EL) : Bool)
      then
        (do
          let w__2 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__2 3 (Mk_AMEVCNTR1_EL0_Type w__3)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_59bacd045e260141 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 4) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__1.EL) : Bool)
      then
        (do
          let w__2 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__2 4 (Mk_AMEVCNTR1_EL0_Type w__3)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_6bd5d306c662d714 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 2) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__1.EL) : Bool)
      then
        (do
          let w__2 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__2 2 (Mk_AMEVCNTR1_EL0_Type w__3)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_887d0ce81624d210 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 15) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__1.EL) : Bool)
      then
        (do
          let w__2 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__2 15 (Mk_AMEVCNTR1_EL0_Type w__3)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_909b4a89534d73e1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 9) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__1.EL) : Bool)
      then
        (do
          let w__2 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__2 9 (Mk_AMEVCNTR1_EL0_Type w__3)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_9193b8497c20a5ba (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 14) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__1.EL) : Bool)
      then
        (do
          let w__2 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__2 14 (Mk_AMEVCNTR1_EL0_Type w__3)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_cef156af264e97db (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 11) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__1.EL) : Bool)
      then
        (do
          let w__2 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__2 11 (Mk_AMEVCNTR1_EL0_Type w__3)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_d8f3e0edb71c094d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 8) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__1.EL) : Bool)
      then
        (do
          let w__2 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__2 8 (Mk_AMEVCNTR1_EL0_Type w__3)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_e45e9615b0ec1e8a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 12) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__1.EL) : Bool)
      then
        (do
          let w__2 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__2 12 (Mk_AMEVCNTR1_EL0_Type w__3)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_f1dd22a5ecbcbc6b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 13) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__1.EL) : Bool)
      then
        (do
          let w__2 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__2 13 (Mk_AMEVCNTR1_EL0_Type w__3)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_fe71412c61f10c5a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 7) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((IsHighestEL w__1.EL) : Bool)
      then
        (do
          let w__2 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__2 7 (Mk_AMEVCNTR1_EL0_Type w__3)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def CNTFRQ_EL0_SysRegWrite_f59bce36e5e3ca32 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((IsHighestEL w__0.EL) : Bool)
  then
    (do
      let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg CNTFRQ_EL0 w__1)
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def CNTHCTL_EL2_SysRegWrite_c57f8627acf05dc2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg CNTKCTL_EL1 (Mk_CNTKCTL_EL1_Type w__2))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg CNTHCTL_EL2 (Mk_CNTHCTL_EL2_Type w__3))
              else
                (do
                  let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg CNTKCTL_EL1 (Mk_CNTKCTL_EL1_Type w__4)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg CNTKCTL_EL1 (Mk_CNTKCTL_EL1_Type w__5))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CPTR_EL3_SysRegWrite_3835d83d048c2034 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg CPTR_EL3 (Mk_CPTR_EL3_Type w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DIT_SysRegWrite_cb82290c1722296d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg PSTATE { w__1 with DIT := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__2 24)])) })
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg PSTATE { w__3 with DIT := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__4
                24)])) })
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
              let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg PSTATE { w__5 with DIT := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                    w__6 24)])) })
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
                  let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg PSTATE { w__7 with DIT := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                        w__8 24)])) })
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DLR_EL0_SysRegWrite_7614507cf751cf9d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (Halted ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg DLR_EL0 w__1)


/-- Type quantifiers: t : Int -/
def DSPSR_EL0_SysRegWrite_2829d14e4c67df55 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (Halted ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg DSPSR_EL0 (Mk_DSPSR_EL0_Type w__1))


/-- Type quantifiers: t : Int -/
def ESR_EL3_SysRegWrite_d8e4dd481971160d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg ESR_EL3 (Mk_ESR_EL3_Type w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def FAR_EL3_SysRegWrite_d150ecea5bb2beb8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg FAR_EL3 w__1)
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def GCSCR_EL3_SysRegWrite_7d39fd6ab827245b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg GCSCR_EL3 (Mk_GCSCR_EL3_Type w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def GCSPR_EL3_SysRegWrite_2c3789955c87eb01 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg GCSPR_EL3 (Mk_GCSPR_EL3_Type w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def GPCCR_EL3_SysRegWrite_34a621e690dc851f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (__set_GPCCR_EL3 (Mk_GPCCR_EL3_Type w__1)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def GPTBR_EL3_SysRegWrite_6f7a8066a1cb6176 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg GPTBR_EL3 (Mk_GPTBR_EL3_Type w__1))
              else (pure (())))))


end ArmFull.Functions
