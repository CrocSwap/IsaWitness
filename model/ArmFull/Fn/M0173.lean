module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0019
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0043
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0045
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0058
public import ArmFull.Fn.M0066
public import ArmFull.Fn.M0075
public import ArmFull.Fn.M0080
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0115
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0151
public import ArmFull.Fn.M0165
public import ArmFull.Fn.M0167
public import ArmFull.Fn.M0168
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0171 set_option backward.proofsInPublic true @[expose] public section

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
def AMEVCNTR1_EL0_SysRegWrite_5139d9a03c76c81b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 3) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (IsHighestEL w__1.EL) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          let w__3 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__3 3 (Mk_AMEVCNTR1_EL0_Type w__4)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_59bacd045e260141 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 4) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (IsHighestEL w__1.EL) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          let w__3 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__3 4 (Mk_AMEVCNTR1_EL0_Type w__4)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_6bd5d306c662d714 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 2) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (IsHighestEL w__1.EL) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          let w__3 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__3 2 (Mk_AMEVCNTR1_EL0_Type w__4)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_887d0ce81624d210 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 15) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (IsHighestEL w__1.EL) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          let w__3 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__3 15 (Mk_AMEVCNTR1_EL0_Type w__4)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_909b4a89534d73e1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 9) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (IsHighestEL w__1.EL) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          let w__3 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__3 9 (Mk_AMEVCNTR1_EL0_Type w__4)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_9193b8497c20a5ba (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 14) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (IsHighestEL w__1.EL) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          let w__3 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__3 14 (Mk_AMEVCNTR1_EL0_Type w__4)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_cef156af264e97db (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 11) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (IsHighestEL w__1.EL) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          let w__3 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__3 11 (Mk_AMEVCNTR1_EL0_Type w__4)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_d8f3e0edb71c094d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 8) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (IsHighestEL w__1.EL) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          let w__3 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__3 8 (Mk_AMEVCNTR1_EL0_Type w__4)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_e45e9615b0ec1e8a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 12) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (IsHighestEL w__1.EL) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          let w__3 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__3 12 (Mk_AMEVCNTR1_EL0_Type w__4)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_f1dd22a5ecbcbc6b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 13) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (IsHighestEL w__1.EL) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          let w__3 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__3 13 (Mk_AMEVCNTR1_EL0_Type w__4)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegWrite_fe71412c61f10c5a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 7) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (IsHighestEL w__1.EL) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          let w__3 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVCNTR1_EL0 (vectorUpdate w__3 7 (Mk_AMEVCNTR1_EL0_Type w__4)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def CNTFRQ_EL0_SysRegWrite_f59bce36e5e3ca32 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (IsHighestEL w__0.EL) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg CNTFRQ_EL0 w__2)
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def RMR_EL1_SysRegWrite_f5cc0dff5c1c57d6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL1) : Bool)))) : Bool)
    then
      (do
        (IsHighestEL EL1))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg RMR_EL1 (Mk_RMR_EL1_Type w__3))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def RMR_EL3_SysRegWrite_d2303115883d7964 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then
      (do
        (IsHighestEL EL3))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg RMR_EL3 (Mk_RMR_EL3_Type w__3))
  else sailThrow ((Error_Undefined ()))


def C40InitRawRegression (_ : Unit) : SailM Unit := do
  writeReg NUM_BREAKPOINTS (Neg.neg 1)
  writeReg NUM_WATCHPOINTS (Neg.neg 1)
  writeReg __num_ctx_breakpoints (Neg.neg 1)
  (InitFeatureImpl ())
  let w__0 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
  ArmFull.assert (w__0 ≥b 2) "sail-inputs/31-armcert-c47-impdef.sail:799.31-799.32"
  let w__1 ← (( do readReg NUM_WATCHPOINTS ) : SailM Int )
  ArmFull.assert (w__1 ≥b 2) "sail-inputs/31-armcert-c47-impdef.sail:800.31-800.32"
  let w__5 ← (( do
    if ((← do
         let w__2 ← (( do readReg __num_ctx_breakpoints ) : SailM Int )
         (pure (((w__2 ≥b 1) : Bool)))) : Bool)
    then
      (do
        let w__3 ← (( do readReg __num_ctx_breakpoints ) : SailM Int )
        let w__4 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
        (pure (((w__3 ≤b w__4) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__5 "sail-inputs/31-armcert-c47-impdef.sail:801.80-801.81"


def IsSecureBelowEL3 (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (HaveEL EL3) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (SCR_GEN_read ()) ) : SailM (BitVec 64) )
      (pure (((_get_SCRType_NS w__1) == 0#1))))
  else
    (do
      let w__6 ← (( do
        if ((← do
             (HaveEL EL2)) : Bool)
        then
          (do
            if ((← do
                 let w__3 ← (( do (HaveSecureEL2Ext ()) ) : SailM Bool )
                 (pure (((! w__3) : Bool)))) : Bool)
            then (pure true)
            else
              (do
                let w__4 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                (pure (((! w__4) : Bool)))))
        else (pure false) ) : SailM Bool )
      if (w__6 : Bool)
      then (pure (false))
      else
        (do
          (__IMPDEF_boolean "Secure-only implementation")))


def __get_FPCR (value_name : (BitVec 64)) : SailM (BitVec 64) := do
  let tmp : FPCR_Type := value_name
  let tmp : FPCR_Type := (Mk_FPCR_Type (tmp &&& (Complement.complement 0xFFFFFFFFF80040F8#64)))
  let w__0 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Invalid Operation floating-point exceptions") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__0) : Bool)
    then
      (Mk_FPCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x100#12 64)))))
    else tmp
  let w__1 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Divide by Zero floating-point exceptions") ) : SailM
    Bool )
  let tmp : (BitVec 64) :=
    if ((! w__1) : Bool)
    then
      (Mk_FPCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x200#12 64)))))
    else tmp
  let w__2 ← (( do (__IMPDEF_boolean "IMPLEMENTED_trapping of Overflow floating-point exceptions")
    ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__2) : Bool)
    then
      (Mk_FPCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x400#12 64)))))
    else tmp
  let w__3 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Underflow floating-point exceptions") ) : SailM Bool
    )
  let tmp : (BitVec 64) :=
    if ((! w__3) : Bool)
    then
      (Mk_FPCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x800#12 64)))))
    else tmp
  let w__4 ← (( do (__IMPDEF_boolean "IMPLEMENTED_trapping of Inexact floating-point exceptions")
    ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__4) : Bool)
    then
      (Mk_FPCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x1000#16 64)))))
    else tmp
  let w__5 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Input Denormal floating-point exceptions") ) : SailM
    Bool )
  let tmp : (BitVec 64) :=
    if ((! w__5) : Bool)
    then
      (Mk_FPCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x8000#16 64)))))
    else tmp
  let w__6 ← (( do (__IMPDEF_boolean "IMPLEMENTED_FPSCR.LEN,STRIDE as RAZ") ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__6 : Bool)
    then
      (Mk_FPCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x370000#24 64)))))
    else tmp
  (pure (tmp))


def __get_FPSCR (value_name : (BitVec 32)) : SailM (BitVec 32) := do
  let tmp : FPSCR_Type := value_name
  let tmp : FPSCR_Type :=
    (Mk_FPSCR_Type
      (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
          (Sail.BitVec.zeroExtend 0x6060#16 32)))))
  let w__0 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Invalid Operation floating-point exceptions") ) :
    SailM Bool )
  let tmp : (BitVec 32) :=
    if ((! w__0) : Bool)
    then
      (Mk_FPSCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
            (Sail.BitVec.zeroExtend 0x100#12 32)))))
    else tmp
  let w__1 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Divide by Zero floating-point exceptions") ) : SailM
    Bool )
  let tmp : (BitVec 32) :=
    if ((! w__1) : Bool)
    then
      (Mk_FPSCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
            (Sail.BitVec.zeroExtend 0x200#12 32)))))
    else tmp
  let w__2 ← (( do (__IMPDEF_boolean "IMPLEMENTED_trapping of Overflow floating-point exceptions")
    ) : SailM Bool )
  let tmp : (BitVec 32) :=
    if ((! w__2) : Bool)
    then
      (Mk_FPSCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
            (Sail.BitVec.zeroExtend 0x400#12 32)))))
    else tmp
  let w__3 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Underflow floating-point exceptions") ) : SailM Bool
    )
  let tmp : (BitVec 32) :=
    if ((! w__3) : Bool)
    then
      (Mk_FPSCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
            (Sail.BitVec.zeroExtend 0x800#12 32)))))
    else tmp
  let w__4 ← (( do (__IMPDEF_boolean "IMPLEMENTED_trapping of Inexact floating-point exceptions")
    ) : SailM Bool )
  let tmp : (BitVec 32) :=
    if ((! w__4) : Bool)
    then
      (Mk_FPSCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
            (Sail.BitVec.zeroExtend 0x1000#16 32)))))
    else tmp
  let w__5 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Input Denormal floating-point exceptions") ) : SailM
    Bool )
  let tmp : (BitVec 32) :=
    if ((! w__5) : Bool)
    then
      (Mk_FPSCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
            (Sail.BitVec.zeroExtend 0x8000#16 32)))))
    else tmp
  let w__6 ← (( do (__IMPDEF_boolean "IMPLEMENTED_FPSCR.LEN,STRIDE as RAZ") ) : SailM Bool )
  let tmp : (BitVec 32) :=
    if (w__6 : Bool)
    then
      (Mk_FPSCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
            (Sail.BitVec.zeroExtend 0x370000#24 32)))))
    else tmp
  (pure (tmp))


def __IMPDEF_integer (x : String) : SailM Int := do
  (ImpDefInt x)


def SecureOnlyImplementation (_ : Unit) : SailM Bool := do
  (__IMPDEF_boolean "Secure-only implementation")


def BRBEFreeze (_ : Unit) : SailM Unit := do
  let w__0 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
  writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__0 7 7 1#1)
  let w__1 ← (( do (BRBETimeStamp ()) ) : SailM TimeStamp )
  let w__2 ← (( do (GetTimestamp w__1) ) : SailM (BitVec 64) )
  writeReg BRBTS_EL1 (Mk_BRBTS_EL1_Type w__2)


def NonSecureOnlyImplementation (_ : Unit) : SailM Bool := do
  (__IMPDEF_boolean "Non-secure only implementation")


def InsertIESBBeforeException (el : (BitVec 2)) : SailM Bool := do
  if ((← do
       (HaveIESB ())) : Bool)
  then
    (do
      (__IMPDEF_boolean "Has Implicit Error Synchronization Barrier before Exception"))
  else (pure false)


def ConditionSyndrome (_ : Unit) : SailM (BitVec 5) := do
  let cond ← (( do (undefined_bitvector_at (← occLabel 725) 4) ) : SailM (BitVec 4) )
  let syndrome ← (( do (undefined_bitvector_at (← occLabel 726) 5) ) : SailM (BitVec 5) )
  let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let cond ← (( do (AArch32_CurrentCond ()) ) : SailM (BitVec 4) )
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__1.T == 0#1) : Bool)
      then
        (do
          let syndrome : (BitVec 5) := (BitVec.update syndrome 4 (Bit 1#1))
          let w__4 ← (( do
            if ((← do
                 (ConditionHolds cond)) : Bool)
            then
              (do
                (ConstrainUnpredictableBool Unpredictable_ESRCONDPASS))
            else (pure false) ) : SailM Bool )
          let syndrome : (BitVec 5) :=
            if (w__4 : Bool)
            then (Sail.BitVec.updateSubrange syndrome 3 0 0b1110#4)
            else (Sail.BitVec.updateSubrange syndrome 3 0 cond)
          (pure (syndrome)))
      else
        (do
          let w__5 ← (( do (__IMPDEF_boolean "Condition valid for trapped T32") ) : SailM Bool )
          if (w__5 : Bool)
          then
            (let syndrome : (BitVec 5) := (BitVec.update syndrome 4 (Bit 1#1))
            let syndrome : (BitVec 5) := (Sail.BitVec.updateSubrange syndrome 3 0 cond)
            (pure (syndrome)))
          else
            (do
              let syndrome : (BitVec 5) := (BitVec.update syndrome 4 (Bit 0#1))
              let w__6 ← (( do (__UNKNOWN_bits 4) ) : SailM (BitVec 4) )
              let syndrome := ((Sail.BitVec.updateSubrange syndrome 3 0 w__6) : (BitVec 5))
              (pure (syndrome)))))
  else
    (let syndrome : (BitVec 5) := (BitVec.update syndrome 4 (Bit 1#1))
    let syndrome : (BitVec 5) := (Sail.BitVec.updateSubrange syndrome 3 0 0b1110#4)
    (pure (syndrome)))


def EL3SDDUndefPriority (_ : Unit) : SailM Bool := do
  if ((← do
       if ((← do
            (Halted ())) : Bool)
       then
         (do
           let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
           (pure ((((_get_EDSCR_Type_SDD w__1) == 1#1) : Bool))))
       else (pure false)) : Bool)
  then
    (do
      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
  else (pure false)


def ICInstNeedsTranslation (opscope : CacheOpScope) : SailM Bool := do
  (__IMPDEF_boolean "Instruction Cache needs translation")


def DCInstNeedsTranslation (opscope : CacheOpScope) : SailM Bool := do
  if ((BEq.beq opscope CacheOpScope_PoE) : Bool)
  then (pure (false))
  else
    (do
      if ((BEq.beq opscope CacheOpScope_PoPA) : Bool)
      then (pure (false))
      else
        (do
          let w__0 ← (( do readReg CLIDR_EL1 ) : SailM (BitVec 64) )
          if (((_get_CLIDR_EL1_Type_LoC w__0) == 0b000#3) : Bool)
          then
            (do
              let w__1 ← (( do
                (__IMPDEF_boolean
                  "No fault generated for DC operations if PoC is before any level of cache") ) :
                SailM Bool )
              (pure ((! w__1))))
          else
            (do
              let w__3 ← (( do
                (pure ((← do
                      let w__2 ← (( do readReg CLIDR_EL1 ) : SailM (BitVec 64) )
                      (pure ((((_get_CLIDR_EL1_Type_LoUU w__2) == 0b000#3) : Bool)))) && ((BEq.beq
                      opscope CacheOpScope_PoU) : Bool))) ) : SailM Bool )
              if (w__3 : Bool)
              then
                (do
                  let w__4 ← (( do
                    (__IMPDEF_boolean
                      "No fault generated for DC operations if PoU is before any level of cache") )
                    : SailM Bool )
                  (pure ((! w__4))))
              else (pure (true)))))


/-- Type quantifiers: k_d_side : Bool -/
def AArch32_FaultSyndrome (d_side : Bool) (fault : FaultRecord) : SailM (BitVec 25) := do
  ArmFull.assert (bne fault.statuscode Fault_None) "sail-inputs/03-v8_base.sail:13653.41-13653.42"
  let iss : (BitVec 25) := (Zeros (n := 25))
  let iss2 : (BitVec 24) := (Zeros (n := 24))
  let w__2 ← (( do
    if ((← do
         (HaveRASExt ())) : Bool)
    then
      (do
        (IsAsyncAbort__1 fault))
    else (pure false) ) : SailM Bool )
  let iss ← (( do
    if (w__2 : Bool)
    then
      (do
        let errstate ← (( do (AArch32_PEErrorState fault) ) : SailM ErrorState )
        let w__3 ← (( do (AArch32_EncodeAsyncErrorSyndrome errstate) ) : SailM (BitVec 2) )
        let iss := ((Sail.BitVec.updateSubrange iss 11 10 w__3) : (BitVec 25))
        (pure (iss)))
    else (pure (iss)) ) : SailM (BitVec 25) )
  let iss ← (( do
    if (d_side : Bool)
    then
      (do
        let w__12 ← (( do
          if ((← do
               (pure ((← do
                     (IsSecondStage fault)) && ((! fault.s2fs1walk) : Bool)))) : Bool)
          then
            (do
              if ((← do
                   let w__6 ← (( do (IsExternalSyncAbort__1 fault) ) : SailM Bool )
                   (pure (((! w__6) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  if ((← do
                       (pure ((← do
                             let w__7 ← (( do (HaveRASExt ()) ) : SailM Bool )
                             (pure (((! w__7) : Bool)))) && ((BEq.beq fault.access.acctype
                             AccessType_TTW) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "ISV on second stage translation table walk"))
                  else (pure false)))
          else (pure false) ) : SailM Bool )
        let iss : (BitVec 25) :=
          if (w__12 : Bool)
          then (Sail.BitVec.updateSubrange iss 24 14 (LSInstructionSyndrome ()))
          else iss
        let iss : (BitVec 25) :=
          if (((BEq.beq fault.access.acctype AccessType_DC) || ((BEq.beq fault.access.acctype
                   AccessType_IC) || (BEq.beq fault.access.acctype AccessType_AT))) : Bool)
          then (BitVec.update iss 8 (Bit 1#1))
          else iss
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
                let w__13 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
                let iss := ((BitVec.update iss 6 (Bit w__13)) : (BitVec 25))
                (pure (iss)))
            else
              (do
                let w__15 ← (( do
                  if ((fault.access.atomicop : Bool) : Bool)
                  then
                    (do
                      (IsExternalAbort__1 fault))
                  else (pure false) ) : SailM Bool )
                if (w__15 : Bool)
                then
                  (do
                    let w__16 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
                    let iss := ((BitVec.update iss 6 (Bit w__16)) : (BitVec 25))
                    (pure (iss)))
                else
                  (let iss : (BitVec 25) :=
                    (BitVec.update iss 6
                      (Bit
                        (if (fault.write : Bool)
                        then 1#1
                        else 0#1)))
                  (pure (iss))))))
    else (pure (iss)) ) : SailM (BitVec 25) )
  let w__17 ← (( do (IsExternalAbort__1 fault) ) : SailM Bool )
  let iss : (BitVec 25) :=
    if (w__17 : Bool)
    then (BitVec.update iss 9 (Bit fault.extflag))
    else iss
  let iss : (BitVec 25) :=
    (BitVec.update iss 7
      (Bit
        (if (fault.s2fs1walk : Bool)
        then 1#1
        else 0#1)))
  let w__18 ← (( do (EncodeLDFSC fault.statuscode fault.level) ) : SailM (BitVec 6) )
  let iss := ((Sail.BitVec.updateSubrange iss 5 0 w__18) : (BitVec 25))
  (pure (iss))


end ArmFull.Functions
