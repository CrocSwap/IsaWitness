module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0043
public import ArmFull.Fn.M0058
public import ArmFull.Fn.M0080
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0124
public import ArmFull.Fn.M0143
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0167
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0172 set_option backward.proofsInPublic true @[expose] public section

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

def __get_PMCR (value_name : (BitVec 32)) : SailM (BitVec 32) := do
  let tmp : PMCR_Type := value_name
  let tmp : PMCR_Type :=
    (Mk_PMCR_Type
      (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
          (Sail.BitVec.zeroExtend 0x506#12 32)))))
  let w__0 ← (( do (__IMPDEF_boolean "the implementation includes a PMU event export bus") ) :
    SailM Bool )
  let tmp : (BitVec 32) :=
    if ((! w__0) : Bool)
    then
      (Mk_PMCR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
            (Sail.BitVec.zeroExtend 0x10#8 32)))))
    else tmp
  let w__1 ← (( do (IsFeatureImplemented FEAT_PMUv3p7) ) : SailM Bool )
  let tmp : (BitVec 32) :=
    if ((! (! w__1)) : Bool)
    then (Mk_PMCR_Type (tmp &&& (Complement.complement 0xFF000000#32)))
    else tmp
  (pure (tmp))


def __get_HSCTLR (value_name : (BitVec 32)) : SailM (BitVec 32) := do
  let tmp : HSCTLR_Type := value_name
  let tmp : HSCTLR_Type :=
    (Mk_HSCTLR_Type
      (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
          (Sail.BitVec.zeroExtend 0x20200#20 32)))))
  let w__0 ← (( do (__IMPDEF_boolean "IMPLEMENTED_CP15BEN") ) : SailM Bool )
  let tmp : (BitVec 32) :=
    if ((! w__0) : Bool)
    then
      (Mk_HSCTLR_Type
        ((Sail.BitVec.castWidth (m := 32) (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
              (Sail.BitVec.zeroExtend 0x0#4 32))))) ||| (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.zeroExtend
            0x20#8 32))))
    else tmp
  let w__1 ← (( do (__IMPDEF_boolean "IMPLEMENTED_ITD") ) : SailM Bool )
  let tmp : (BitVec 32) :=
    if ((! w__1) : Bool)
    then
      (Mk_HSCTLR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
            (Sail.BitVec.zeroExtend 0x80#8 32)))))
    else tmp
  (pure (tmp))


def __get_SCTLR (value_name : (BitVec 32)) : SailM (BitVec 32) := do
  let tmp : SCTLR_Type := value_name
  let tmp : SCTLR_Type :=
    (Mk_SCTLR_Type
      (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
          (Sail.BitVec.zeroExtend 0x20000#20 32)))))
  let w__0 ← (( do (__IMPDEF_boolean "IMPLEMENTED_CP15BEN") ) : SailM Bool )
  let tmp : (BitVec 32) :=
    if ((! w__0) : Bool)
    then
      (Mk_SCTLR_Type
        ((Sail.BitVec.castWidth (m := 32) (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
              (Sail.BitVec.zeroExtend 0x0#4 32))))) ||| (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.zeroExtend
            0x20#8 32))))
    else tmp
  let w__1 ← (( do (__IMPDEF_boolean "IMPLEMENTED_ITD") ) : SailM Bool )
  let tmp : (BitVec 32) :=
    if ((! w__1) : Bool)
    then
      (Mk_SCTLR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
            (Sail.BitVec.zeroExtend 0x80#8 32)))))
    else tmp
  (pure (tmp))


def __get_SCTLR_NS (value_name : (BitVec 32)) : SailM (BitVec 32) := do
  let tmp : SCTLR_Type := value_name
  let tmp : SCTLR_Type :=
    (Mk_SCTLR_Type
      (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
          (Sail.BitVec.zeroExtend 0x20000#20 32)))))
  let w__0 ← (( do (__IMPDEF_boolean "IMPLEMENTED_CP15BEN") ) : SailM Bool )
  let tmp : (BitVec 32) :=
    if ((! w__0) : Bool)
    then
      (Mk_SCTLR_Type
        ((Sail.BitVec.castWidth (m := 32) (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
              (Sail.BitVec.zeroExtend 0x0#4 32))))) ||| (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.zeroExtend
            0x20#8 32))))
    else tmp
  let w__1 ← (( do (__IMPDEF_boolean "IMPLEMENTED_ITD") ) : SailM Bool )
  let tmp : (BitVec 32) :=
    if ((! w__1) : Bool)
    then
      (Mk_SCTLR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
            (Sail.BitVec.zeroExtend 0x80#8 32)))))
    else tmp
  (pure (tmp))


def __get_SCTLR_S (value_name : (BitVec 32)) : SailM (BitVec 32) := do
  let tmp : SCTLR_Type := value_name
  let tmp : SCTLR_Type :=
    (Mk_SCTLR_Type
      (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
          (Sail.BitVec.zeroExtend 0x20000#20 32)))))
  let w__0 ← (( do (__IMPDEF_boolean "IMPLEMENTED_CP15BEN") ) : SailM Bool )
  let tmp : (BitVec 32) :=
    if ((! w__0) : Bool)
    then
      (Mk_SCTLR_Type
        ((Sail.BitVec.castWidth (m := 32) (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
              (Sail.BitVec.zeroExtend 0x0#4 32))))) ||| (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.zeroExtend
            0x20#8 32))))
    else tmp
  let w__1 ← (( do (__IMPDEF_boolean "IMPLEMENTED_ITD") ) : SailM Bool )
  let tmp : (BitVec 32) :=
    if ((! w__1) : Bool)
    then
      (Mk_SCTLR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
            (Sail.BitVec.zeroExtend 0x80#8 32)))))
    else tmp
  (pure (tmp))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_017c244c296ed80f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 5) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__4 ← (( do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (IsHighestEL w__1.EL)) : Bool)
        then
          (do
            let w__3 ← (( do (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed") ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__5 ← (( do readReg AMEVTYPER1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVTYPER1_EL0 (vectorUpdate w__5 5 (Mk_AMEVTYPER1_EL0_Type w__6)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_15f530ac1097257c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 13) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__4 ← (( do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (IsHighestEL w__1.EL)) : Bool)
        then
          (do
            let w__3 ← (( do (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed") ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__5 ← (( do readReg AMEVTYPER1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVTYPER1_EL0 (vectorUpdate w__5 13 (Mk_AMEVTYPER1_EL0_Type w__6)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_3a4a4f972b395f75 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 12) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__4 ← (( do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (IsHighestEL w__1.EL)) : Bool)
        then
          (do
            let w__3 ← (( do (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed") ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__5 ← (( do readReg AMEVTYPER1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVTYPER1_EL0 (vectorUpdate w__5 12 (Mk_AMEVTYPER1_EL0_Type w__6)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_622d8153064a03a6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 2) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__4 ← (( do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (IsHighestEL w__1.EL)) : Bool)
        then
          (do
            let w__3 ← (( do (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed") ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__5 ← (( do readReg AMEVTYPER1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVTYPER1_EL0 (vectorUpdate w__5 2 (Mk_AMEVTYPER1_EL0_Type w__6)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_6269036dfbd59a24 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 9) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__4 ← (( do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (IsHighestEL w__1.EL)) : Bool)
        then
          (do
            let w__3 ← (( do (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed") ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__5 ← (( do readReg AMEVTYPER1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVTYPER1_EL0 (vectorUpdate w__5 9 (Mk_AMEVTYPER1_EL0_Type w__6)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_7e132038a6af9b7c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 8) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__4 ← (( do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (IsHighestEL w__1.EL)) : Bool)
        then
          (do
            let w__3 ← (( do (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed") ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__5 ← (( do readReg AMEVTYPER1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVTYPER1_EL0 (vectorUpdate w__5 8 (Mk_AMEVTYPER1_EL0_Type w__6)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_85fbd4e6563d2700 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 15) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__4 ← (( do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (IsHighestEL w__1.EL)) : Bool)
        then
          (do
            let w__3 ← (( do (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed") ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__5 ← (( do readReg AMEVTYPER1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVTYPER1_EL0 (vectorUpdate w__5 15 (Mk_AMEVTYPER1_EL0_Type w__6)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_8b9bd86620491fc7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 11) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__4 ← (( do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (IsHighestEL w__1.EL)) : Bool)
        then
          (do
            let w__3 ← (( do (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed") ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__5 ← (( do readReg AMEVTYPER1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVTYPER1_EL0 (vectorUpdate w__5 11 (Mk_AMEVTYPER1_EL0_Type w__6)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_a9e61442f4e1c8cd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 6) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__4 ← (( do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (IsHighestEL w__1.EL)) : Bool)
        then
          (do
            let w__3 ← (( do (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed") ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__5 ← (( do readReg AMEVTYPER1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVTYPER1_EL0 (vectorUpdate w__5 6 (Mk_AMEVTYPER1_EL0_Type w__6)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_bc02f6fe6d8b784f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 7) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__4 ← (( do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (IsHighestEL w__1.EL)) : Bool)
        then
          (do
            let w__3 ← (( do (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed") ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__5 ← (( do readReg AMEVTYPER1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVTYPER1_EL0 (vectorUpdate w__5 7 (Mk_AMEVTYPER1_EL0_Type w__6)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_be5c5b889ae5d0cb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 1) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__4 ← (( do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (IsHighestEL w__1.EL)) : Bool)
        then
          (do
            let w__3 ← (( do (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed") ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__5 ← (( do readReg AMEVTYPER1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVTYPER1_EL0 (vectorUpdate w__5 1 (Mk_AMEVTYPER1_EL0_Type w__6)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_c43b886db277fa04 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 0) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__4 ← (( do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (IsHighestEL w__1.EL)) : Bool)
        then
          (do
            let w__3 ← (( do (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed") ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__5 ← (( do readReg AMEVTYPER1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVTYPER1_EL0 (vectorUpdate w__5 0 (Mk_AMEVTYPER1_EL0_Type w__6)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_e549f9ca48c70852 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 14) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__4 ← (( do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (IsHighestEL w__1.EL)) : Bool)
        then
          (do
            let w__3 ← (( do (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed") ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__5 ← (( do readReg AMEVTYPER1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVTYPER1_EL0 (vectorUpdate w__5 14 (Mk_AMEVTYPER1_EL0_Type w__6)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_ed2615d4120abbd7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 3) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__4 ← (( do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (IsHighestEL w__1.EL)) : Bool)
        then
          (do
            let w__3 ← (( do (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed") ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__5 ← (( do readReg AMEVTYPER1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVTYPER1_EL0 (vectorUpdate w__5 3 (Mk_AMEVTYPER1_EL0_Type w__6)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_f55a7574a9b217fe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 4) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__4 ← (( do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (IsHighestEL w__1.EL)) : Bool)
        then
          (do
            let w__3 ← (( do (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed") ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__5 ← (( do readReg AMEVTYPER1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVTYPER1_EL0 (vectorUpdate w__5 4 (Mk_AMEVTYPER1_EL0_Type w__6)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegWrite_f744e58350c3c492 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (IsG1ActivityMonitorImplemented 10) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__4 ← (( do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (IsHighestEL w__1.EL)) : Bool)
        then
          (do
            let w__3 ← (( do (__IMPDEF_boolean "AMEVCNTR1_EL0[m] is fixed") ) : SailM Bool )
            (pure (((! w__3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__5 ← (( do readReg AMEVTYPER1_EL0 ) : SailM (Vector (BitVec 64) 16) )
          let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg AMEVTYPER1_EL0 (vectorUpdate w__5 10 (Mk_AMEVTYPER1_EL0_Type w__6)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def JMCR_SysRegWrite32_5cdfe87c581e3185 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__1 ← (( do (__IMPDEF_boolean "JMCR UNDEFINED at EL0") ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (())))
  else
    (pure (if ((__PSTATE_EL == EL1) : Bool)
      then ()
      else
        (if ((__PSTATE_EL == EL2) : Bool)
        then ()
        else
          (if ((__PSTATE_EL == EL3) : Bool)
          then ()
          else ()))))


/-- Type quantifiers: t : Int -/
def JOSCR_SysRegWrite32_88e20b8662c98b9c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__1 ← (( do (__IMPDEF_boolean "JOSCR UNDEFINED at EL0") ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (())))
  else
    (pure (if ((__PSTATE_EL == EL1) : Bool)
      then ()
      else
        (if ((__PSTATE_EL == EL2) : Bool)
        then ()
        else
          (if ((__PSTATE_EL == EL3) : Bool)
          then ()
          else ()))))


def decode_aarch32_instrs_SB_T1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SB_Op_A_txt ()))
  else (pure (()))


def decode_aarch32_instrs_SETPAN_T1enc_A_txt (imm1 : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let w__1 ← (( do (HavePANExt ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let value_name : (BitVec 1) := imm1
  (execute_aarch32_instrs_SETPAN_Op_A_txt value_name)


def decode_aarch32_instrs_TSB_T1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HaveSelfHostedTrace ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then
        (do
          (EndOfInstruction ()))
      else (pure (()))
      let w__2 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__2 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (pure ((execute_aarch32_instrs_TSB_Op_A_txt ()))))
  else (pure (()))


def decode_aarch32_instrs_CSDB_T1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_CSDB_Op_A_txt ()))
  else (pure (()))


end ArmFull.Functions
