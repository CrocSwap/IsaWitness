import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0020
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0054
import ArmFull.Fn.M0056
import ArmFull.Fn.M0057
import ArmFull.Fn.M0062
import ArmFull.Fn.M0144
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0180
import ArmFull.Fn.M0181
import ArmFull.Fn.M0186
import ArmFull.Fn.M0189

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


def SPE_PMBIDR_P_Read (_ : Unit) : SailM (BitVec 1) := do
  let owning_ss ← (( do (undefined_SecurityState (← occLabel 2447) ()) ) : SailM SecurityState )
  let owning_el ← (( do (undefined_bitvector_at (← occLabel 2448) 2) ) : SailM (BitVec 2) )
  let w__0 ← (( do (ProfilingBufferOwner ()) ) : SailM (SecurityState × (BitVec 2)) )
  let (tup__0, tup__1) := (w__0 : (SecurityState × (BitVec 2)))
  let owning_ss : SecurityState := tup__0
  let owning_el : (BitVec 2) := tup__1
  let w__5 ← (( do
    if ((← do
         let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure ((((BitVec.toNat owning_el) >b (BitVec.toNat w__1.EL)) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__2.EL != EL3) : Bool)))) : Bool)
        then
          (do
            let w__3 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
            (pure (((bne owning_ss w__3) : Bool))))
        else (pure false)) ) : SailM Bool )
  let w__6 : (BitVec 1) :=
    if (w__5 : Bool)
    then 1#1
    else 0#1
  (pure (w__6))


def DACR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_DACR_Type (← occLabel 2579) ()) ) : SailM DACR_Type )
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
      readReg DACR_S)
  else
    (do
      (DACR_NS_read ()))


def BankedRegisterAccessValid (SYSm : (BitVec 5)) (mode : (BitVec 5)) : SailM Unit := do
  let b__0 := SYSm
  if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 4 2)) == (0b000#3 : (BitVec 3))) : Bool)
  then
    (do
      if ((mode != M32_FIQ) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (())))
  else
    (do
      match b__0 with
      | 0b00100 =>
        (do
          if ((mode != M32_FIQ) : Bool)
          then sailThrow ((Error_Unpredictable ()))
          else (pure (())))
      | 0b00101 =>
        (do
          if ((mode == M32_System) : Bool)
          then sailThrow ((Error_Unpredictable ()))
          else (pure (())))
      | 0b00110 =>
        (do
          if (((mode == M32_Hyp) || (mode == M32_System)) : Bool)
          then sailThrow ((Error_Unpredictable ()))
          else (pure (())))
      | b__0 =>
        (do
          if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 4 2)) == (0b010#3 : (BitVec 3))) : Bool)
          then
            (do
              if ((mode == M32_FIQ) : Bool)
              then sailThrow ((Error_Unpredictable ()))
              else (pure (())))
          else
            (do
              if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 4 1)) == (0x6#4 : (BitVec 4))) : Bool)
              then
                (do
                  if ((mode == M32_FIQ) : Bool)
                  then sailThrow ((Error_Unpredictable ()))
                  else (pure (())))
              else
                (do
                  match b__0 with
                  | 0b01110 =>
                    (do
                      if ((mode == M32_FIQ) : Bool)
                      then sailThrow ((Error_Unpredictable ()))
                      else (pure (())))
                  | b__0 =>
                    (do
                      if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 4 1)) == (0x8#4 : (BitVec 4))) : Bool)
                      then
                        (do
                          if ((mode == M32_IRQ) : Bool)
                          then sailThrow ((Error_Unpredictable ()))
                          else (pure (())))
                      else
                        (do
                          if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 4 1)) == (0x9#4 : (BitVec 4))) : Bool)
                          then
                            (do
                              if ((mode == M32_Svc) : Bool)
                              then sailThrow ((Error_Unpredictable ()))
                              else (pure (())))
                          else
                            (do
                              if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 4 1)) == (0xA#4 : (BitVec 4))) : Bool)
                              then
                                (do
                                  if ((mode == M32_Abort) : Bool)
                                  then sailThrow ((Error_Unpredictable ()))
                                  else (pure (())))
                              else
                                (do
                                  if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0
                                         4 1)) == (0xB#4 : (BitVec 4))) : Bool)
                                  then
                                    (do
                                      if ((mode == M32_Undef) : Bool)
                                      then sailThrow ((Error_Unpredictable ()))
                                      else (pure (())))
                                  else
                                    (do
                                      if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                             b__0 4 1)) == (0xE#4 : (BitVec 4))) : Bool)
                                      then
                                        (do
                                          let w__2 ← (( do
                                            (pure ((← do
                                                  if (((! (HaveEL EL3)) : Bool) : Bool)
                                                  then (pure true)
                                                  else
                                                    (do
                                                      let w__0 ← (( do (CurrentSecurityState ()) )
                                                        : SailM SecurityState )
                                                      (pure (((bne w__0 SS_Secure) : Bool))))) || ((mode == M32_Monitor) : Bool)))
                                            ) : SailM Bool )
                                          if (w__2 : Bool)
                                          then sailThrow ((Error_Unpredictable ()))
                                          else (pure (())))
                                      else
                                        (do
                                          match b__0 with
                                          | 0b11110 =>
                                            (do
                                              if (((! (HaveEL EL2)) || (! ((mode == M32_Monitor) || (mode == M32_Hyp)))) : Bool)
                                              then sailThrow ((Error_Unpredictable ()))
                                              else (pure (())))
                                          | 0b11111 =>
                                            (do
                                              if (((! (HaveEL EL2)) || (mode != M32_Monitor)) : Bool)
                                              then sailThrow ((Error_Unpredictable ()))
                                              else (pure (())))
                                          | _ => sailThrow ((Error_Unpredictable ()))))))))))))


def CPSRWriteByInstr (value_name : (BitVec 32)) (bytemask : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let privileged : Bool := (w__0.EL != EL0)
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access bytemask 3)])) == 1#1) : Bool)
  then
    (do
      let split_vec := (Sail.BitVec.extractLsb value_name 31 27)
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with N := (Sail.BitVec.extractLsb split_vec 4 4) }
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with Z := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with C := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with V := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with Q := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access bytemask 2)])) == 1#1) : Bool)
  then
    (do
      let w__6 ← (( do (HaveSSBSExt ()) ) : SailM Bool )
      if (w__6 : Bool)
      then
        (do
          let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__7 with SSBS := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                value_name 23)])) })
      else (pure (()))
      if (privileged : Bool)
      then
        (do
          let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__8 with PAN := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                value_name 22)])) })
      else (pure (()))
      let w__9 ← (( do (HaveDITExt ()) ) : SailM Bool )
      if (w__9 : Bool)
      then
        (do
          let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__10 with DIT := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                value_name 21)])) })
      else (pure (()))
      let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__11 with GE := (Sail.BitVec.extractLsb value_name 19 16) })
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access bytemask 1)])) == 1#1) : Bool)
  then
    (do
      let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__12 with E := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access value_name
            9)])) }
      if (privileged : Bool)
      then
        (do
          let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__13 with A := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                value_name 8)])) })
      else (pure (())))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access bytemask 0)])) == 1#1) : Bool)
  then
    (do
      if (privileged : Bool)
      then
        (do
          let split_vec := (Sail.BitVec.extractLsb value_name 7 6)
          let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__14 with I := (Sail.BitVec.extractLsb split_vec 1 1) }
          let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__15 with F := (Sail.BitVec.extractLsb split_vec 0 0) }
          (AArch32_WriteModeByInstr (Sail.BitVec.extractLsb value_name 4 0)))
      else (pure (())))
  else (pure (()))


end ArmFull.Functions
