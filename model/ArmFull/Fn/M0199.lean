module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0020
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0053
public import ArmFull.Fn.M0054
public import ArmFull.Fn.M0055
public import ArmFull.Fn.M0056
public import ArmFull.Fn.M0057
public import ArmFull.Fn.M0167
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0179
public import ArmFull.Fn.M0187 set_option backward.proofsInPublic true @[expose] public section

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

def CSSELR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_CSSELR_Type (← occLabel 2128) ()) ) : SailM CSSELR_Type )
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
      readReg CSSELR_S)
  else
    (do
      (CSSELR_NS_read ()))


def CSSELR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CSSELR_Type := value_name
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
      writeReg CSSELR_S r)
  else
    (do
      (CSSELR_NS_write r))


def DFSR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_DFSR_Type (← occLabel 2142) ()) ) : SailM DFSR_Type )
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
      readReg DFSR_S)
  else
    (do
      (DFSR_NS_read ()))


def ICC_BPR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_ICC_BPR1_Type (← occLabel 2160) ()) ) : SailM ICC_BPR1_Type )
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
      (ICC_BPR1_S_read ()))
  else
    (do
      (ICC_BPR1_NS_read ()))


def ICC_BPR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_BPR1_Type := value_name
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
      (ICC_BPR1_S_write r))
  else
    (do
      (ICC_BPR1_NS_write r))


def ICC_CTLR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_ICC_CTLR_Type (← occLabel 2163) ()) ) : SailM ICC_CTLR_Type )
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
      (ICC_CTLR_S_read ()))
  else
    (do
      (ICC_CTLR_NS_read ()))


def ICC_CTLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_CTLR_Type := value_name
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
      (ICC_CTLR_S_write r))
  else
    (do
      (ICC_CTLR_NS_write r))


def ICC_IGRPEN1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_ICC_IGRPEN1_Type (← occLabel 2184) ()) ) : SailM ICC_IGRPEN1_Type )
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
      (ICC_IGRPEN1_S_read ()))
  else
    (do
      (ICC_IGRPEN1_NS_read ()))


def ICC_IGRPEN1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_IGRPEN1_Type := value_name
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
      (ICC_IGRPEN1_S_write r))
  else
    (do
      (ICC_IGRPEN1_NS_write r))


def ICC_SRE_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_ICC_SRE_Type (← occLabel 2194) ()) ) : SailM ICC_SRE_Type )
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
      (ICC_SRE_S_read ()))
  else
    (do
      (ICC_SRE_NS_read ()))


def ICC_SRE_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_SRE_Type := value_name
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
      (ICC_SRE_S_write r))
  else
    (do
      (ICC_SRE_NS_write r))


def IFSR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_IFSR_Type (← occLabel 2245) ()) ) : SailM IFSR_Type )
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
      readReg IFSR_S)
  else
    (do
      (IFSR_NS_read ()))


def PAR_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do (undefined_PAR_Type (← occLabel 2253) ()) ) : SailM PAR_Type )
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
      readReg PAR_S)
  else
    (do
      readReg PAR_NS)


def PAR_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : PAR_Type := value_name
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
      writeReg PAR_S r)
  else
    (do
      writeReg PAR_NS r)


def PRRR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_PRRR_Type (← occLabel 2265) ()) ) : SailM PRRR_Type )
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
      readReg PRRR_S)
  else
    (do
      (PRRR_NS_read ()))


def PRRR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PRRR_Type := value_name
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
      writeReg PRRR_S r)
  else
    (do
      (PRRR_NS_write r))


def SCTLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : SCTLR_Type := value_name
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
      writeReg SCTLR_S r)
  else
    (do
      (SCTLR_NS_write r))


def TTBCR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_TTBCR2_Type (← occLabel 2272) ()) ) : SailM TTBCR2_Type )
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
      readReg TTBCR2_S)
  else
    (do
      (TTBCR2_NS_read ()))


def TTBCR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TTBCR2_Type := value_name
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
      writeReg TTBCR2_S r)
  else
    (do
      (TTBCR2_NS_write r))


def TTBCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TTBCR_Type := value_name
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
      writeReg TTBCR_S r)
  else
    (do
      (TTBCR_NS_write r))


def TTBR0_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : TTBR0_Type := value_name
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
      writeReg TTBR0_S r)
  else
    (do
      writeReg TTBR0_NS r)


def TTBR1_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : TTBR1_Type := value_name
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
      writeReg TTBR1_S r)
  else
    (do
      writeReg TTBR1_NS r)


def VBAR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : VBAR_Type := value_name
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
      writeReg VBAR_S r)
  else
    (do
      (VBAR_NS_write r))


def NMRR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_NMRR_Type (← occLabel 2315) ()) ) : SailM NMRR_Type )
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
      readReg NMRR_S)
  else
    (do
      (NMRR_NS_read ()))


def NMRR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : NMRR_Type := value_name
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
      writeReg NMRR_S r)
  else
    (do
      (NMRR_NS_write r))


def ICC_BPR1_EL1_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do (undefined_ICC_BPR1_EL1_Type (← occLabel 2383) ()) ) : SailM ICC_BPR1_EL1_Type )
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
      readReg ICC_BPR1_EL1_S)
  else
    (do
      readReg ICC_BPR1_EL1_NS)


def ICC_BPR1_EL1_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : ICC_BPR1_EL1_Type := value_name
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
      writeReg ICC_BPR1_EL1_S r)
  else
    (do
      writeReg ICC_BPR1_EL1_NS r)


def ICC_CTLR_EL1_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do (undefined_ICC_CTLR_EL1_Type (← occLabel 2384) ()) ) : SailM ICC_CTLR_EL1_Type )
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
      readReg ICC_CTLR_EL1_S)
  else
    (do
      readReg ICC_CTLR_EL1_NS)


def ICC_CTLR_EL1_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : ICC_CTLR_EL1_Type := value_name
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
      writeReg ICC_CTLR_EL1_S r)
  else
    (do
      writeReg ICC_CTLR_EL1_NS r)


def ICC_IGRPEN1_EL1_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do (undefined_ICC_IGRPEN1_EL1_Type (← occLabel 2385) ()) ) : SailM
    ICC_IGRPEN1_EL1_Type )
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
      readReg ICC_IGRPEN1_EL1_S)
  else
    (do
      readReg ICC_IGRPEN1_EL1_NS)


def ICC_IGRPEN1_EL1_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : ICC_IGRPEN1_EL1_Type := value_name
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
      writeReg ICC_IGRPEN1_EL1_S r)
  else
    (do
      writeReg ICC_IGRPEN1_EL1_NS r)


def ICC_SRE_EL1_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do (undefined_ICC_SRE_EL1_Type (← occLabel 2386) ()) ) : SailM ICC_SRE_EL1_Type )
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
      readReg ICC_SRE_EL1_S)
  else
    (do
      readReg ICC_SRE_EL1_NS)


def ICC_SRE_EL1_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : ICC_SRE_EL1_Type := value_name
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
      writeReg ICC_SRE_EL1_S r)
  else
    (do
      writeReg ICC_SRE_EL1_NS r)


def DebugTarget (_ : Unit) : SailM (BitVec 2) := do
  let ss ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
  (DebugTargetFrom ss)


def SPESampleAddAddressPCVirtual (_ : Unit) : SailM Unit := do
  let this_address ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let w__0 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
  let w__1 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
  writeReg SPESampleAddress (vectorUpdate w__0 SPEAddrPosPCVirtual
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__1 SPEAddrPosPCVirtual) 55 0
      (Sail.BitVec.extractLsb this_address 55 0)))
  let ns ← (( do (undefined_bitvector_at (.site 2424) 1) ) : SailM (BitVec 1) )
  let nse ← (( do (undefined_bitvector_at (.site 2425) 1) ) : SailM (BitVec 1) )
  let w__2 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
  let (ns, nse) ← (( do
    match w__2 with
    | .SS_Secure =>
      (let ns : (BitVec 1) := 0#1
      let nse : (BitVec 1) := 0#1
      (pure ((ns, nse))))
    | .SS_NonSecure =>
      (let ns : (BitVec 1) := 1#1
      let nse : (BitVec 1) := 0#1
      (pure ((ns, nse))))
    | .SS_Realm =>
      (let ns : (BitVec 1) := 1#1
      let nse : (BitVec 1) := 1#1
      (pure ((ns, nse))))
    | _ =>
      (do
        (Unreachable ())
        (pure ((ns, nse)))) ) : SailM ((BitVec 1) × (BitVec 1)) )
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  let el : (BitVec 2) := w__3.EL
  let w__4 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
  let w__5 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
  writeReg SPESampleAddress (vectorUpdate w__4 SPEAddrPosPCVirtual
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__5 SPEAddrPosPCVirtual) 63 56
      (((ns +++ el) +++ nse) +++ (Zeros (n := 4)))))
  let w__6 ← (( do readReg SPESampleAddressValid ) : SailM (Vector Bool 32) )
  writeReg SPESampleAddressValid (vectorUpdate w__6 SPEAddrPosPCVirtual true)


end ArmFull.Functions
