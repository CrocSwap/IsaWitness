import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0016
import ArmFull.Fn.M0023
import ArmFull.Fn.M0046
import ArmFull.Fn.M0056
import ArmFull.Fn.M0058
import ArmFull.Fn.M0087
import ArmFull.Fn.M0197
import ArmFull.Fn.M0200

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

def PAR_EL1_read (_ : Unit) : SailM (BitVec 128) := do
  let r ← (( do readReg _PAR_EL1 ) : SailM PAR_EL1_Type )
  let w__0 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 63 0 (BitVec.slice w__0 0 64)) : (BitVec 128))
  (pure (r))


def PAR_EL1_write (value_name : (BitVec 128)) : SailM Unit := do
  let r : PAR_EL1_Type := value_name
  let w__0 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
  (PAR_write (Mk_PAR_Type (set_slice 64 w__0 0 (BitVec.slice r 0 64))))
  writeReg _PAR_EL1 r


def TTBR0_EL1_write (value_name : (BitVec 128)) : SailM Unit := do
  let r : TTBR0_EL1_Type := value_name
  let w__0 ← (( do (TTBR0_read ()) ) : SailM (BitVec 64) )
  (TTBR0_write (Mk_TTBR0_Type (set_slice 64 w__0 0 (BitVec.slice r 0 64))))
  writeReg _TTBR0_EL1 r


def TTBR1_EL1_write (value_name : (BitVec 128)) : SailM Unit := do
  let r : TTBR1_EL1_Type := value_name
  let w__0 ← (( do (TTBR1_read ()) ) : SailM (BitVec 64) )
  (TTBR1_write (Mk_TTBR1_Type (set_slice 64 w__0 0 (BitVec.slice r 0 64))))
  writeReg _TTBR1_EL1 r


/-- Type quantifiers: k_cold : Bool -/
def AArch64_AutoGen_ArchitectureReset__seg1 (cold : Bool) : SailM Bool := do
  let w__308 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__308 3 3 0#1)
  let w__309 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__309 2 2 0#1)
  let w__310 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__310 1 1 0#1)
  let w__311 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__311 0 0 0#1)
  let w__312 ← (( do readReg ICC_SGI0R_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_SGI0R_EL1 (Sail.BitVec.updateSubrange w__312 63 56 0b00000000#8)
  let w__313 ← (( do readReg ICC_SGI0R_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_SGI0R_EL1 (Sail.BitVec.updateSubrange w__313 43 41 0b000#3)
  let w__314 ← (( do readReg ICC_SGI0R_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_SGI0R_EL1 (Sail.BitVec.updateSubrange w__314 31 28 0b0000#4)
  let w__315 ← (( do readReg FPCR ) : SailM (BitVec 64) )
  writeReg FPCR (Sail.BitVec.updateSubrange w__315 63 27 0b0000000000000000000000000000000000000#37)
  let w__316 ← (( do readReg FPCR ) : SailM (BitVec 64) )
  writeReg FPCR (BitVec.update w__316 14 (Bit 0#1))
  let w__317 ← (( do readReg FPCR ) : SailM (BitVec 64) )
  writeReg FPCR (Sail.BitVec.updateSubrange w__317 7 3 0b00000#5)
  let w__318 ← (( do readReg CNTHVS_CTL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHVS_CTL_EL2 (Sail.BitVec.updateSubrange w__318 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  let w__319 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__319 23 20 0b0000#4)
  let w__320 ← (( do readReg ICC_DIR_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_DIR_EL1 (Sail.BitVec.updateSubrange w__320 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__321 ← (( do readReg SDER32_EL2 ) : SailM (BitVec 64) )
  writeReg SDER32_EL2 (Sail.BitVec.updateSubrange w__321 63 2
    0b00000000000000000000000000000000000000000000000000000000000000#62)
  let w__322 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
  writeReg VSTCR_EL2 (Sail.BitVec.updateSubrange w__322 63 34 0b000000000000000000000000000000#30)
  let w__323 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
  writeReg VSTCR_EL2 (BitVec.update w__323 32 (Bit 0#1))
  let w__324 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
  writeReg VSTCR_EL2 (BitVec.update w__324 31 (Bit 1#1))
  let w__325 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
  writeReg VSTCR_EL2 (Sail.BitVec.updateSubrange w__325 28 16 0b0000000000000#13)
  let w__326 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
  writeReg VSTCR_EL2 (Sail.BitVec.updateSubrange w__326 13 8 0b000000#6)
  let w__327 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__327 3 0 0b0000#4)
  let w__328 ← (( do readReg PMMIR_EL1 ) : SailM (BitVec 64) )
  writeReg PMMIR_EL1 (Sail.BitVec.updateSubrange w__328 63 28
    0b000000000000000000000000000000000000#36)
  let w__329 ← (( do readReg ICV_IAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_IAR0_EL1 (Sail.BitVec.updateSubrange w__329 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__330 ← (( do (ICC_IGRPEN1_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_IGRPEN1_EL1_write
    (Mk_ICC_IGRPEN1_EL1_Type
      (set_slice 63 w__330 1 0b000000000000000000000000000000000000000000000000000000000000000#63)))
  let w__331 ← (( do (ICC_IGRPEN1_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_IGRPEN1_EL1_write (_update_ICC_IGRPEN1_EL1_Type_Enable w__331 0#1))
  let w__332 ← (( do readReg GPTBR_EL3 ) : SailM (BitVec 64) )
  writeReg GPTBR_EL3 (Sail.BitVec.updateSubrange w__332 63 40 0b000000000000000000000000#24)
  let w__333 ← (( do readReg MDCCSR_EL0 ) : SailM (BitVec 64) )
  writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange w__333 63 31
    0b000000000000000000000000000000000#33)
  let w__334 ← (( do readReg MDCCSR_EL0 ) : SailM (BitVec 64) )
  writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange w__334 28 19 0b0000000000#10)
  let w__335 ← (( do readReg MDCCSR_EL0 ) : SailM (BitVec 64) )
  writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange w__335 18 15 0b0000#4)
  let w__336 ← (( do readReg MDCCSR_EL0 ) : SailM (BitVec 64) )
  writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange w__336 14 13 0b00#2)
  let w__337 ← (( do readReg MDCCSR_EL0 ) : SailM (BitVec 64) )
  writeReg MDCCSR_EL0 (BitVec.update w__337 12 (Bit 0#1))
  let w__338 ← (( do readReg MDCCSR_EL0 ) : SailM (BitVec 64) )
  writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange w__338 11 6 0b000000#6)
  let w__339 ← (( do readReg MDCCSR_EL0 ) : SailM (BitVec 64) )
  writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange w__339 5 2 0b0000#4)
  let w__340 ← (( do readReg MDCCSR_EL0 ) : SailM (BitVec 64) )
  writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange w__340 1 0 0b00#2)
  let w__341 ← (( do readReg ID_MMFR5_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR5_EL1 (Sail.BitVec.updateSubrange w__341 63 8
    0b00000000000000000000000000000000000000000000000000000000#56)
  let w__342 ← (( do readReg ID_MMFR5_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR5_EL1 (Sail.BitVec.updateSubrange w__342 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__343 ← (( do readReg TTBR0_EL3 ) : SailM (BitVec 64) )
  writeReg TTBR0_EL3 (Sail.BitVec.updateSubrange w__343 63 56 0b00000000#8)
  let w__344 ← (( do readReg TTBR0_EL3 ) : SailM (BitVec 64) )
  writeReg TTBR0_EL3 (Sail.BitVec.updateSubrange w__344 4 3 0b00#2)
  let w__345 ← (( do readReg TTBR0_EL3 ) : SailM (BitVec 64) )
  writeReg TTBR0_EL3 (Sail.BitVec.updateSubrange w__345 63 48 0b0000000000000000#16)
  let w__346 ← (( do readReg PMCCFILTR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCCFILTR_EL0 (Sail.BitVec.updateSubrange w__346 63 32
    0b00000000000000000000000000000000#32)
  let w__347 ← (( do readReg PMCCFILTR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCCFILTR_EL0 (BitVec.update w__347 25 (Bit 0#1))
  let w__348 ← (( do readReg PMCCFILTR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCCFILTR_EL0 (Sail.BitVec.updateSubrange w__348 19 0 0b00000000000000000000#20)
  let w__349 ← (( do readReg ICC_NMIAR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_NMIAR1_EL1 (Sail.BitVec.updateSubrange w__349 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__350 ← (( do readReg DBGCLAIMSET_EL1 ) : SailM (BitVec 64) )
  writeReg DBGCLAIMSET_EL1 (Sail.BitVec.updateSubrange w__350 63 32
    0b00000000000000000000000000000000#32)
  let w__351 ← (( do readReg DBGCLAIMSET_EL1 ) : SailM (BitVec 64) )
  writeReg DBGCLAIMSET_EL1 (Sail.BitVec.updateSubrange w__351 31 8 0b000000000000000000000000#24)
  let w__352 ← (( do (ICC_SRE_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_SRE_EL1_write
    (Mk_ICC_SRE_EL1_Type
      (set_slice 61 w__352 3 0b0000000000000000000000000000000000000000000000000000000000000#61)))
  let w__353 ← (( do (ICC_SRE_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_SRE_EL1_write (_update_ICC_SRE_EL1_Type_DIB w__353 0#1))
  let w__354 ← (( do (ICC_SRE_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_SRE_EL1_write (_update_ICC_SRE_EL1_Type_DFB w__354 0#1))
  let w__355 ← (( do (ICC_SRE_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_SRE_EL1_write (_update_ICC_SRE_EL1_Type_SRE w__355 0#1))
  let w__356 ← (( do readReg ICC_IAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_IAR0_EL1 (Sail.BitVec.updateSubrange w__356 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__357 ← (( do readReg ESR_EL2 ) : SailM (BitVec 64) )
  writeReg ESR_EL2 (Sail.BitVec.updateSubrange w__357 63 56 0b00000000#8)
  let w__358 ← (( do readReg CONTEXTIDR_EL1 ) : SailM (BitVec 64) )
  writeReg CONTEXTIDR_EL1 (Sail.BitVec.updateSubrange w__358 63 32
    0b00000000000000000000000000000000#32)
  let w__359 ← (( do readReg ID_ISAR4_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR4_EL1 (Sail.BitVec.updateSubrange w__359 63 32
    0b00000000000000000000000000000000#32)
  let w__360 ← (( do readReg ID_ISAR4_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR4_EL1 (Sail.BitVec.updateSubrange w__360 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__361 ← (( do readReg ID_ISAR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR1_EL1 (Sail.BitVec.updateSubrange w__361 63 32
    0b00000000000000000000000000000000#32)
  let w__362 ← (( do readReg ID_ISAR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR1_EL1 (Sail.BitVec.updateSubrange w__362 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__363 ← (( do readReg PMUACR_EL1 ) : SailM (BitVec 64) )
  writeReg PMUACR_EL1 (Sail.BitVec.updateSubrange w__363 63 33 0b0000000000000000000000000000000#31)
  let w__364 ← (( do readReg DSPSR_EL0 ) : SailM (BitVec 64) )
  writeReg DSPSR_EL0 (Sail.BitVec.updateSubrange w__364 63 34 0b000000000000000000000000000000#30)
  let w__365 ← (( do readReg DSPSR_EL0 ) : SailM (BitVec 64) )
  writeReg DSPSR_EL0 (BitVec.update w__365 32 (Bit 0#1))
  let w__366 ← (( do readReg DSPSR_EL0 ) : SailM (BitVec 64) )
  writeReg DSPSR_EL0 (Sail.BitVec.updateSubrange w__366 63 35 0b00000000000000000000000000000#29)
  let w__367 ← (( do readReg DSPSR_EL0 ) : SailM (BitVec 64) )
  writeReg DSPSR_EL0 (Sail.BitVec.updateSubrange w__367 27 26 0b00#2)
  let w__368 ← (( do readReg DSPSR_EL0 ) : SailM (BitVec 64) )
  writeReg DSPSR_EL0 (Sail.BitVec.updateSubrange w__368 19 14 0b000000#6)
  let w__369 ← (( do readReg DSPSR_EL0 ) : SailM (BitVec 64) )
  writeReg DSPSR_EL0 (BitVec.update w__369 5 (Bit 0#1))
  let w__370 ← (( do readReg RMR_EL2 ) : SailM (BitVec 64) )
  writeReg RMR_EL2 (Sail.BitVec.updateSubrange w__370 63 2
    0b00000000000000000000000000000000000000000000000000000000000000#62)
  let w__371 ← (( do readReg RMR_EL2 ) : SailM (BitVec 64) )
  writeReg RMR_EL2 (Sail.BitVec.updateSubrange w__371 1 1 0#1)
  let w__372 ← (( do readReg VNCR_EL2 ) : SailM (BitVec 64) )
  writeReg VNCR_EL2 (Sail.BitVec.updateSubrange w__372 11 0 0b000000000000#12)
  let w__373 ← (( do readReg PMINTENCLR_EL1 ) : SailM (BitVec 64) )
  writeReg PMINTENCLR_EL1 (Sail.BitVec.updateSubrange w__373 63 33
    0b0000000000000000000000000000000#31)
  let w__374 ← (( do readReg PMINTENCLR_EL1 ) : SailM (BitVec 64) )
  writeReg PMINTENCLR_EL1 (BitVec.update w__374 32 (Bit 0#1))
  let w__375 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
  writeReg PMSELR_EL0 (Sail.BitVec.updateSubrange w__375 63 5
    0b00000000000000000000000000000000000000000000000000000000000#59)
  let w__376 ← (( do (ICC_CTLR_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_CTLR_EL1_write
    (Mk_ICC_CTLR_EL1_Type (set_slice 44 w__376 20 0b00000000000000000000000000000000000000000000#44)))
  let w__377 ← (( do (ICC_CTLR_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_CTLR_EL1_write (Mk_ICC_CTLR_EL1_Type (set_slice 2 w__377 16 0b00#2)))
  let w__378 ← (( do (ICC_CTLR_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_CTLR_EL1_write (Mk_ICC_CTLR_EL1_Type (set_slice 1 w__378 7 0#1)))
  let w__379 ← (( do (ICC_CTLR_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_CTLR_EL1_write (Mk_ICC_CTLR_EL1_Type (set_slice 4 w__379 2 0b0000#4)))
  let w__380 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange w__380 63 32
    0b00000000000000000000000000000000#32)
  let w__381 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange w__381 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__382 ← (( do readReg CNTP_CTL_EL0 ) : SailM (BitVec 64) )
  writeReg CNTP_CTL_EL0 (Sail.BitVec.updateSubrange w__382 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  let w__383 ← (( do readReg HFGITR2_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR2_EL2 (Sail.BitVec.updateSubrange w__383 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__384 ← (( do readReg CNTHV_TVAL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHV_TVAL_EL2 (Sail.BitVec.updateSubrange w__384 63 32
    0b00000000000000000000000000000000#32)
  let w__385 ← (( do readReg SPSR_irq ) : SailM (BitVec 64) )
  writeReg SPSR_irq (Sail.BitVec.updateSubrange w__385 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__386 ← (( do readReg SPSR_irq ) : SailM (BitVec 64) )
  writeReg SPSR_irq (Sail.BitVec.updateSubrange w__386 63 32 0b00000000000000000000000000000000#32)
  let w__387 ← (( do readReg ICH_MISR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_MISR_EL2 (Sail.BitVec.updateSubrange w__387 63 8
    0b00000000000000000000000000000000000000000000000000000000#56)
  let w__388 ← (( do readReg ICH_MISR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_MISR_EL2 (Sail.BitVec.updateSubrange w__388 7 7 0#1)
  let w__389 ← (( do readReg ICH_MISR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_MISR_EL2 (Sail.BitVec.updateSubrange w__389 6 6 0#1)
  let w__390 ← (( do readReg ICH_MISR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_MISR_EL2 (Sail.BitVec.updateSubrange w__390 5 5 0#1)
  let w__391 ← (( do readReg ICH_MISR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_MISR_EL2 (Sail.BitVec.updateSubrange w__391 4 4 0#1)
  let w__392 ← (( do readReg ICH_MISR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_MISR_EL2 (Sail.BitVec.updateSubrange w__392 3 3 0#1)
  let w__393 ← (( do readReg ICH_MISR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_MISR_EL2 (Sail.BitVec.updateSubrange w__393 2 2 0#1)
  let w__394 ← (( do readReg ICH_MISR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_MISR_EL2 (Sail.BitVec.updateSubrange w__394 1 1 0#1)
  let w__395 ← (( do readReg ICH_MISR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_MISR_EL2 (Sail.BitVec.updateSubrange w__395 0 0 0#1)
  let w__396 ← (( do readReg CSSELR_EL1 ) : SailM (BitVec 64) )
  writeReg CSSELR_EL1 (Sail.BitVec.updateSubrange w__396 63 5
    0b00000000000000000000000000000000000000000000000000000000000#59)
  let w__397 ← (( do readReg ICV_RPR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_RPR_EL1 (Sail.BitVec.updateSubrange w__397 62 8
    0b0000000000000000000000000000000000000000000000000000000#55)
  let w__398 ← (( do readReg PFAR_EL2 ) : SailM (BitVec 64) )
  writeReg PFAR_EL2 (Sail.BitVec.updateSubrange w__398 61 56 0b000000#6)
  let w__399 ← (( do readReg ICV_PMR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_PMR_EL1 (Sail.BitVec.updateSubrange w__399 63 8
    0b00000000000000000000000000000000000000000000000000000000#56)
  let w__400 ← (( do readReg MFAR_EL3 ) : SailM (BitVec 64) )
  writeReg MFAR_EL3 (Sail.BitVec.updateSubrange w__400 61 56 0b000000#6)
  let w__401 ← (( do readReg MFAR_EL3 ) : SailM (BitVec 64) )
  writeReg MFAR_EL3 (Sail.BitVec.updateSubrange w__401 11 0 0b000000000000#12)
  let w__402 ← (( do readReg MFAR_EL3 ) : SailM (BitVec 64) )
  writeReg MFAR_EL3 (Sail.BitVec.updateSubrange w__402 61 56 0b000000#6)
  let w__403 ← (( do readReg SPSR_EL2 ) : SailM (BitVec 64) )
  writeReg SPSR_EL2 (Sail.BitVec.updateSubrange w__403 63 34 0b000000000000000000000000000000#30)
  let w__404 ← (( do readReg SPSR_EL2 ) : SailM (BitVec 64) )
  writeReg SPSR_EL2 (BitVec.update w__404 32 (Bit 0#1))
  let w__405 ← (( do readReg SPSR_EL2 ) : SailM (BitVec 64) )
  writeReg SPSR_EL2 (Sail.BitVec.updateSubrange w__405 63 35 0b00000000000000000000000000000#29)
  let w__406 ← (( do readReg SPSR_EL2 ) : SailM (BitVec 64) )
  writeReg SPSR_EL2 (Sail.BitVec.updateSubrange w__406 27 26 0b00#2)
  let w__407 ← (( do readReg SPSR_EL2 ) : SailM (BitVec 64) )
  writeReg SPSR_EL2 (Sail.BitVec.updateSubrange w__407 19 14 0b000000#6)
  let w__408 ← (( do readReg SPSR_EL2 ) : SailM (BitVec 64) )
  writeReg SPSR_EL2 (BitVec.update w__408 5 (Bit 0#1))
  let w__409 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
  writeReg TCR_EL1 (Sail.BitVec.updateSubrange w__409 63 62 0b00#2)
  let w__410 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
  writeReg TCR_EL1 (BitVec.update w__410 35 (Bit 0#1))
  let w__411 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
  writeReg TCR_EL1 (BitVec.update w__411 6 (Bit 0#1))
  let w__412 ← (( do readReg ICV_HPPIR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_HPPIR0_EL1 (Sail.BitVec.updateSubrange w__412 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__413 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
  writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__413 63 7
    0b000000000000000000000000000000000000000000000000000000000#57)
  if ((((! cold) && (! (HaveEL EL2))) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__414 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
      writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__414 6 6 0#1))
  else
    (do
      let w__415 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
      let w__416 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__415 6 6 w__416))
  if ((((! cold) && (! (HaveEL EL2))) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__417 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
      writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__417 5 5 0#1))
  else
    (do
      let w__418 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
      let w__419 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__418 5 5 w__419))
  if ((((! cold) && (! (HaveEL EL2))) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__420 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
      writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__420 4 4 0#1))
  else
    (do
      let w__421 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
      let w__422 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__421 4 4 w__422))
  if ((((! cold) && (! (HaveEL EL2))) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__423 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
      writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__423 3 3 0#1))
  else
    (do
      let w__424 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
      let w__425 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__424 3 3 w__425))
  if ((((! cold) && (! (HaveEL EL2))) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__426 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
      writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__426 2 2 0#1))
  else
    (do
      let w__427 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
      let w__428 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__427 2 2 w__428))
  let w__429 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
  writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__429 1 0 0b00#2)
  let w__430 ← (( do readReg ICV_BPR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_BPR0_EL1 (Sail.BitVec.updateSubrange w__430 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  let w__431 ← (( do readReg ISR_EL1 ) : SailM (BitVec 64) )
  writeReg ISR_EL1 (Sail.BitVec.updateSubrange w__431 63 11
    0b00000000000000000000000000000000000000000000000000000#53)
  let w__432 ← (( do readReg ISR_EL1 ) : SailM (BitVec 64) )
  writeReg ISR_EL1 (Sail.BitVec.updateSubrange w__432 5 0 0b000000#6)
  let w__433 ← (( do readReg ID_ISAR3_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR3_EL1 (Sail.BitVec.updateSubrange w__433 63 32
    0b00000000000000000000000000000000#32)
  let w__434 ← (( do readReg ID_ISAR3_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR3_EL1 (Sail.BitVec.updateSubrange w__434 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__435 ← (( do readReg MECIDR_EL2 ) : SailM (BitVec 64) )
  writeReg MECIDR_EL2 (Sail.BitVec.updateSubrange w__435 63 4
    0b000000000000000000000000000000000000000000000000000000000000#60)
  let w__436 ← (( do readReg PMINTENSET_EL1 ) : SailM (BitVec 64) )
  writeReg PMINTENSET_EL1 (Sail.BitVec.updateSubrange w__436 63 33
    0b0000000000000000000000000000000#31)
  let w__437 ← (( do readReg PMINTENSET_EL1 ) : SailM (BitVec 64) )
  writeReg PMINTENSET_EL1 (BitVec.update w__437 32 (Bit 0#1))
  let w__438 ← (( do readReg SMIDR_EL1 ) : SailM (BitVec 64) )
  writeReg SMIDR_EL1 (Sail.BitVec.updateSubrange w__438 63 32 0b00000000000000000000000000000000#32)
  let w__439 ← (( do readReg SMIDR_EL1 ) : SailM (BitVec 64) )
  writeReg SMIDR_EL1 (Sail.BitVec.updateSubrange w__439 14 12 0b000#3)
  let w__440 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__440 63 63 0#1)
  let w__441 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__441 62 62 0#1)
  let w__442 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__442 61 61 0#1)
  let w__443 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__443 60 60 0#1)
  let w__444 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__444 59 59 0#1)
  let w__445 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__445 58 58 0#1)
  let w__446 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__446 57 57 0#1)
  let w__447 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__447 56 56 0#1)
  let w__448 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__448 55 55 0#1)
  let w__449 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__449 54 54 0#1)
  let w__450 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__450 53 53 0#1)
  let w__451 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__451 52 52 0#1)
  let w__452 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (BitVec.update w__452 51 (Bit 0#1))
  let w__453 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__453 50 50 0#1)
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__454 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__454 49 49 0#1))
  else
    (do
      let w__455 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      let w__456 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__455 49 49 w__456))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__457 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__457 48 48 0#1))
  else
    (do
      let w__458 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      let w__459 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__458 48 48 w__459))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__460 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__460 47 47 0#1))
  else
    (do
      let w__461 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      let w__462 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__461 47 47 w__462))
  let w__463 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (BitVec.update w__463 46 (Bit 0#1))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__464 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__464 45 45 0#1))
  else
    (do
      let w__465 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      let w__466 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__465 45 45 w__466))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__467 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__467 44 44 0#1))
  else
    (do
      let w__468 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      let w__469 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__468 44 44 w__469))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__470 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__470 43 43 0#1))
  else
    (do
      let w__471 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      let w__472 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__471 43 43 w__472))
  let w__473 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (BitVec.update w__473 42 (Bit 0#1))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__474 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__474 41 41 0#1))
  else
    (do
      let w__475 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      let w__476 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__475 41 41 w__476))
  let w__477 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (BitVec.update w__477 40 (Bit 0#1))
  let w__478 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__478 39 39 0#1)
  let w__479 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__479 38 38 0#1)
  let w__480 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__480 37 37 0#1)
  let w__481 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__481 36 36 0#1)
  let w__482 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__482 35 35 0#1)
  let w__483 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__483 34 34 0#1)
  let w__484 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__484 33 33 0#1)
  let w__485 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__485 32 32 0#1)
  let w__486 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__486 31 31 0#1)
  let w__487 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__487 30 30 0#1)
  let w__488 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__488 29 29 0#1)
  let w__489 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (BitVec.update w__489 28 (Bit 0#1))
  let w__490 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__490 27 27 0#1)
  let w__491 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__491 26 25 0b00#2)
  let w__492 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__492 24 24 0#1)
  let w__493 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__493 23 23 0#1)
  let w__494 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__494 22 22 0#1)
  let w__495 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (BitVec.update w__495 21 (Bit 0#1))
  let w__496 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__496 20 20 0#1)
  let w__497 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__497 19 19 0#1)
  let w__498 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (BitVec.update w__498 18 (Bit 0#1))
  let w__499 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__499 17 17 0#1)
  let w__500 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__500 16 16 0#1)
  let w__501 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__501 15 14 0b00#2)
  let w__502 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__502 13 13 0#1)
  let w__503 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__503 12 12 0#1)
  let w__504 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__504 11 11 0#1)
  let w__505 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__505 10 9 0b00#2)
  let w__506 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__506 8 8 0#1)
  let w__507 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__507 7 7 0#1)
  let w__508 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__508 6 6 0#1)
  let w__509 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__509 5 5 0#1)
  let w__510 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__510 4 4 0#1)
  let w__511 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__511 3 3 0#1)
  let w__512 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (BitVec.update w__512 2 (Bit 0#1))
  let w__513 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__513 1 1 0#1)
  let w__514 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__514 0 0 0#1)
  let w__515 ← (( do readReg SMPRI_EL1 ) : SailM (BitVec 64) )
  writeReg SMPRI_EL1 (Sail.BitVec.updateSubrange w__515 63 4
    0b000000000000000000000000000000000000000000000000000000000000#60)
  let w__516 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
  writeReg PMUSERENR_EL0 (Sail.BitVec.updateSubrange w__516 63 7
    0b000000000000000000000000000000000000000000000000000000000#57)
  let w__517 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__517 63 7
    0b000000000000000000000000000000000000000000000000000000000#57)
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__518 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__518 6 6 0#1))
  else
    (do
      let w__519 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      let w__520 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__519 6 6 w__520))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__521 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__521 5 5 0#1))
  else
    (do
      let w__522 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      let w__523 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__522 5 5 w__523))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__524 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__524 4 4 0#1))
  else
    (do
      let w__525 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      let w__526 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__525 4 4 w__526))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__527 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__527 3 3 0#1))
  else
    (do
      let w__528 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      let w__529 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__528 3 3 w__529))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__530 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__530 2 2 0#1))
  else
    (do
      let w__531 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      let w__532 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__531 2 2 w__532))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__533 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__533 1 1 0#1))
  else
    (do
      let w__534 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      let w__535 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__534 1 1 w__535))
  let w__536 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR2_EL2 (BitVec.update w__536 0 (Bit 0#1))
  let w__537 ← (( do readReg PMOVSSET_EL0 ) : SailM (BitVec 64) )
  writeReg PMOVSSET_EL0 (Sail.BitVec.updateSubrange w__537 63 33
    0b0000000000000000000000000000000#31)
  let w__538 ← (( do readReg PMOVSSET_EL0 ) : SailM (BitVec 64) )
  writeReg PMOVSSET_EL0 (BitVec.update w__538 32 (Bit 0#1))
  let w__539 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (BitVec.update w__539 63 (Bit 0#1))
  let w__540 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__540 61 61 0#1)
  let w__541 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (BitVec.update w__541 60 (Bit 0#1))
  let w__542 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__542 58 54 0b00000#5)
  let w__543 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (BitVec.update w__543 52 (Bit 0#1))
  let w__544 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__544 50 45 0b000000#6)
  let w__545 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (BitVec.update w__545 42 (Bit 0#1))
  let w__546 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__546 39 38 0b00#2)
  let w__547 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__547 35 32 0b0000#4)
  let w__548 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__548 29 28 0b11#2)
  let w__549 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (BitVec.update w__549 26 (Bit 0#1))
  let w__550 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (BitVec.update w__550 24 (Bit 0#1))
  let w__551 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (BitVec.update w__551 23 (Bit 1#1))
  let w__552 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (BitVec.update w__552 20 (Bit 0#1))
  let w__553 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (BitVec.update w__553 18 (Bit 1#1))
  let w__554 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (BitVec.update w__554 17 (Bit 0#1))
  let w__555 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (BitVec.update w__555 16 (Bit 1#1))
  let w__556 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__556 15 14 0b00#2)
  let w__557 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__557 12 12 0#1)
  let w__558 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__558 10 7 0b0000#4)
  let w__559 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__559 5 4 0b11#2)
  let w__560 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__560 2 2 0#1)
  let w__561 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__561 0 0 0#1)
  let w__562 ← (( do readReg VBAR_EL1 ) : SailM (BitVec 64) )
  writeReg VBAR_EL1 (Sail.BitVec.updateSubrange w__562 10 0 0b00000000000#11)
  let w__563 ← (( do readReg CNTFRQ_EL0 ) : SailM (BitVec 64) )
  writeReg CNTFRQ_EL0 (Sail.BitVec.updateSubrange w__563 63 32 0b00000000000000000000000000000000#32)
  let w__564 ← (( do readReg ICV_CTLR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange w__564 63 20
    0b00000000000000000000000000000000000000000000#44)
  let w__565 ← (( do readReg ICV_CTLR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange w__565 17 16 0b00#2)
  let w__566 ← (( do readReg ICV_CTLR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange w__566 7 2 0b000000#6)
  let w__567 ← (( do readReg MECID_A0_EL2 ) : SailM (BitVec 64) )
  writeReg MECID_A0_EL2 (Sail.BitVec.updateSubrange w__567 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__568 ← (( do readReg ICV_IAR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_IAR1_EL1 (Sail.BitVec.updateSubrange w__568 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__569 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
  writeReg CPACR_EL1 (Sail.BitVec.updateSubrange w__569 63 30
    0b0000000000000000000000000000000000#34)
  let w__570 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
  writeReg CPACR_EL1 (Sail.BitVec.updateSubrange w__570 27 26 0b00#2)
  let w__571 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
  writeReg CPACR_EL1 (Sail.BitVec.updateSubrange w__571 23 22 0b00#2)
  let w__572 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
  writeReg CPACR_EL1 (Sail.BitVec.updateSubrange w__572 19 18 0b00#2)
  let w__573 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
  writeReg CPACR_EL1 (Sail.BitVec.updateSubrange w__573 15 0 0b0000000000000000#16)
  let w__574 ← (( do readReg DBGDTRRX_EL0 ) : SailM (BitVec 64) )
  writeReg DBGDTRRX_EL0 (Sail.BitVec.updateSubrange w__574 63 32
    0b00000000000000000000000000000000#32)
  let w__575 ← (( do readReg SPSR_EL1 ) : SailM (BitVec 64) )
  writeReg SPSR_EL1 (Sail.BitVec.updateSubrange w__575 63 34 0b000000000000000000000000000000#30)
  let w__576 ← (( do readReg SPSR_EL1 ) : SailM (BitVec 64) )
  writeReg SPSR_EL1 (BitVec.update w__576 32 (Bit 0#1))
  let w__577 ← (( do readReg SPSR_EL1 ) : SailM (BitVec 64) )
  writeReg SPSR_EL1 (Sail.BitVec.updateSubrange w__577 63 35 0b00000000000000000000000000000#29)
  let w__578 ← (( do readReg SPSR_EL1 ) : SailM (BitVec 64) )
  writeReg SPSR_EL1 (Sail.BitVec.updateSubrange w__578 27 26 0b00#2)
  let w__579 ← (( do readReg SPSR_EL1 ) : SailM (BitVec 64) )
  writeReg SPSR_EL1 (Sail.BitVec.updateSubrange w__579 19 14 0b000000#6)
  let w__580 ← (( do readReg SPSR_EL1 ) : SailM (BitVec 64) )
  writeReg SPSR_EL1 (BitVec.update w__580 5 (Bit 0#1))
  let w__581 ← (( do readReg FPEXC32_EL2 ) : SailM (BitVec 64) )
  writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange w__581 63 32
    0b00000000000000000000000000000000#32)
  let w__582 ← (( do readReg FPEXC32_EL2 ) : SailM (BitVec 64) )
  writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange w__582 25 11 0b000000000000000#15)
  let w__583 ← (( do readReg FPEXC32_EL2 ) : SailM (BitVec 64) )
  writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange w__583 6 5 0b00#2)
  let w__584 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__584 63 36 0b0000000000000000000000000000#28)
  if (cold : Bool)
  then
    (do
      let w__585 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
      writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__585 35 35 0#1))
  else (pure (()))
  let w__586 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (BitVec.update w__586 33 (Bit 0#1))
  if ((((! cold) && (! (HaveEL EL2))) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__587 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
      writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__587 32 32 0#1))
  else
    (do
      let w__588 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
      let w__589 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__588 32 32 w__589))
  let w__590 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (BitVec.update w__590 28 (Bit 0#1))
  let w__591 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__591 25 24 0b00#2)
  let w__592 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (BitVec.update w__592 20 (Bit 0#1))
  let w__593 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__593 18 16 0b000#3)
  let w__594 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__594 11 7 0b00000#5)
  let w__595 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__595 5 1 0b00000#5)
  let w__596 ← (( do readReg SPSR_fiq ) : SailM (BitVec 64) )
  writeReg SPSR_fiq (Sail.BitVec.updateSubrange w__596 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__597 ← (( do readReg SPSR_fiq ) : SailM (BitVec 64) )
  writeReg SPSR_fiq (Sail.BitVec.updateSubrange w__597 63 32 0b00000000000000000000000000000000#32)
  let w__598 ← (( do readReg MECID_P0_EL2 ) : SailM (BitVec 64) )
  writeReg MECID_P0_EL2 (Sail.BitVec.updateSubrange w__598 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__599 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
  writeReg GPCCR_EL3 (Sail.BitVec.updateSubrange w__599 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__600 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
  writeReg GPCCR_EL3 (Sail.BitVec.updateSubrange w__600 19 18 0b00#2)
  let w__601 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
  writeReg GPCCR_EL3 (Sail.BitVec.updateSubrange w__601 16 16 0#1)
  let w__602 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
  writeReg GPCCR_EL3 (Sail.BitVec.updateSubrange w__602 7 3 0b00000#5)
  let w__603 ← (( do readReg ID_PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR0_EL1 (Sail.BitVec.updateSubrange w__603 63 32
    0b00000000000000000000000000000000#32)
  let w__604 ← (( do readReg ID_PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR0_EL1 (Sail.BitVec.updateSubrange w__604 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__605 ← (( do readReg MVFR1_EL1 ) : SailM (BitVec 64) )
  writeReg MVFR1_EL1 (Sail.BitVec.updateSubrange w__605 63 32 0b00000000000000000000000000000000#32)
  let w__606 ← (( do readReg MVFR1_EL1 ) : SailM (BitVec 64) )
  writeReg MVFR1_EL1 (Sail.BitVec.updateSubrange w__606 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__607 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__607 63 22
    0b000000000000000000000000000000000000000000#42)
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__608 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__608 21 21 0#1))
  else
    (do
      let w__609 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__610 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__609 21 21 w__610))
  let w__611 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR2_EL2 (BitVec.update w__611 20 (Bit 0#1))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__612 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__612 19 19 0#1))
  else
    (do
      let w__613 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__614 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__613 19 19 w__614))
  let w__615 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__615 18 17 0b00#2)
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__616 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__616 16 16 0#1))
  else
    (do
      let w__617 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__618 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__617 16 16 w__618))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__619 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__619 15 15 0#1))
  else
    (do
      let w__620 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__621 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__620 15 15 w__621))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__622 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__622 14 14 0#1))
  else
    (do
      let w__623 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__624 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__623 14 14 w__624))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__625 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__625 13 13 0#1))
  else
    (do
      let w__626 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__627 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__626 13 13 w__627))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__628 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__628 12 12 0#1))
  else
    (do
      let w__629 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__630 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__629 12 12 w__630))
  (pure true)


end ArmFull.Functions
