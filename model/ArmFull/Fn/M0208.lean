module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0056
public import ArmFull.Fn.M0058
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0196
public import ArmFull.Fn.M0199 set_option backward.proofsInPublic true @[expose] public section

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
  let w__354 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__354 21 21 0#1)
  let w__355 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__355 20 20 0#1)
  let w__356 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__356 19 19 0#1)
  let w__357 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__357 18 18 0#1)
  let w__358 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__358 17 17 0#1)
  let w__359 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__359 16 16 0#1)
  let w__360 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__360 15 15 0#1)
  let w__361 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__361 14 14 0#1)
  let w__362 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__362 13 13 0#1)
  let w__363 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__363 12 12 0#1)
  let w__364 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__364 11 11 0#1)
  let w__365 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__365 10 10 0#1)
  let w__366 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__366 9 9 0#1)
  let w__367 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__367 8 8 0#1)
  let w__368 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__368 7 7 0#1)
  let w__369 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__369 6 6 0#1)
  let w__370 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__370 5 5 0#1)
  let w__371 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__371 4 4 0#1)
  let w__372 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__372 3 3 0#1)
  let w__373 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__373 2 2 0#1)
  let w__374 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__374 1 1 0#1)
  let w__375 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__375 0 0 0#1)
  let w__376 ← (( do readReg ICC_SGI0R_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_SGI0R_EL1 (Sail.BitVec.updateSubrange w__376 63 56 0b00000000#8)
  let w__377 ← (( do readReg ICC_SGI0R_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_SGI0R_EL1 (Sail.BitVec.updateSubrange w__377 43 41 0b000#3)
  let w__378 ← (( do readReg ICC_SGI0R_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_SGI0R_EL1 (Sail.BitVec.updateSubrange w__378 31 28 0b0000#4)
  let w__379 ← (( do readReg FPCR ) : SailM (BitVec 64) )
  writeReg FPCR (Sail.BitVec.updateSubrange w__379 63 27 0b0000000000000000000000000000000000000#37)
  let w__380 ← (( do readReg FPCR ) : SailM (BitVec 64) )
  writeReg FPCR (BitVec.update w__380 14 (Bit 0#1))
  let w__381 ← (( do readReg FPCR ) : SailM (BitVec 64) )
  writeReg FPCR (Sail.BitVec.updateSubrange w__381 7 3 0b00000#5)
  let w__382 ← (( do readReg CNTHVS_CTL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHVS_CTL_EL2 (Sail.BitVec.updateSubrange w__382 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  let w__383 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__383 23 20 0b0000#4)
  let w__384 ← (( do readReg ICC_DIR_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_DIR_EL1 (Sail.BitVec.updateSubrange w__384 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__385 ← (( do readReg SDER32_EL2 ) : SailM (BitVec 64) )
  writeReg SDER32_EL2 (Sail.BitVec.updateSubrange w__385 63 2
    0b00000000000000000000000000000000000000000000000000000000000000#62)
  let w__386 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
  writeReg VSTCR_EL2 (Sail.BitVec.updateSubrange w__386 63 34 0b000000000000000000000000000000#30)
  let w__387 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
  writeReg VSTCR_EL2 (BitVec.update w__387 32 (Bit 0#1))
  let w__388 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
  writeReg VSTCR_EL2 (BitVec.update w__388 31 (Bit 1#1))
  let w__389 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
  writeReg VSTCR_EL2 (Sail.BitVec.updateSubrange w__389 28 16 0b0000000000000#13)
  let w__390 ← (( do readReg VSTCR_EL2 ) : SailM (BitVec 64) )
  writeReg VSTCR_EL2 (Sail.BitVec.updateSubrange w__390 13 8 0b000000#6)
  let w__391 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__391 3 0 0b0000#4)
  let w__392 ← (( do readReg PMMIR_EL1 ) : SailM (BitVec 64) )
  writeReg PMMIR_EL1 (Sail.BitVec.updateSubrange w__392 63 28
    0b000000000000000000000000000000000000#36)
  let w__393 ← (( do readReg ICV_IAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_IAR0_EL1 (Sail.BitVec.updateSubrange w__393 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__394 ← (( do (ICC_IGRPEN1_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_IGRPEN1_EL1_write
    (Mk_ICC_IGRPEN1_EL1_Type
      (set_slice 63 w__394 1 0b000000000000000000000000000000000000000000000000000000000000000#63)))
  let w__395 ← (( do (ICC_IGRPEN1_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_IGRPEN1_EL1_write (_update_ICC_IGRPEN1_EL1_Type_Enable w__395 0#1))
  let w__396 ← (( do readReg GPTBR_EL3 ) : SailM (BitVec 64) )
  writeReg GPTBR_EL3 (Sail.BitVec.updateSubrange w__396 63 40 0b000000000000000000000000#24)
  let w__397 ← (( do readReg MDCCSR_EL0 ) : SailM (BitVec 64) )
  writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange w__397 63 31
    0b000000000000000000000000000000000#33)
  let w__398 ← (( do readReg MDCCSR_EL0 ) : SailM (BitVec 64) )
  writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange w__398 28 19 0b0000000000#10)
  let w__399 ← (( do readReg MDCCSR_EL0 ) : SailM (BitVec 64) )
  writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange w__399 18 15 0b0000#4)
  let w__400 ← (( do readReg MDCCSR_EL0 ) : SailM (BitVec 64) )
  writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange w__400 14 13 0b00#2)
  let w__401 ← (( do readReg MDCCSR_EL0 ) : SailM (BitVec 64) )
  writeReg MDCCSR_EL0 (BitVec.update w__401 12 (Bit 0#1))
  let w__402 ← (( do readReg MDCCSR_EL0 ) : SailM (BitVec 64) )
  writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange w__402 11 6 0b000000#6)
  let w__403 ← (( do readReg MDCCSR_EL0 ) : SailM (BitVec 64) )
  writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange w__403 5 2 0b0000#4)
  let w__404 ← (( do readReg MDCCSR_EL0 ) : SailM (BitVec 64) )
  writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange w__404 1 0 0b00#2)
  let w__405 ← (( do readReg ID_MMFR5_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR5_EL1 (Sail.BitVec.updateSubrange w__405 63 8
    0b00000000000000000000000000000000000000000000000000000000#56)
  let w__406 ← (( do readReg ID_MMFR5_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR5_EL1 (Sail.BitVec.updateSubrange w__406 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__407 ← (( do readReg TTBR0_EL3 ) : SailM (BitVec 64) )
  writeReg TTBR0_EL3 (Sail.BitVec.updateSubrange w__407 63 56 0b00000000#8)
  let w__408 ← (( do readReg TTBR0_EL3 ) : SailM (BitVec 64) )
  writeReg TTBR0_EL3 (Sail.BitVec.updateSubrange w__408 4 3 0b00#2)
  let w__409 ← (( do readReg TTBR0_EL3 ) : SailM (BitVec 64) )
  writeReg TTBR0_EL3 (Sail.BitVec.updateSubrange w__409 63 48 0b0000000000000000#16)
  let w__410 ← (( do readReg PMCCFILTR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCCFILTR_EL0 (Sail.BitVec.updateSubrange w__410 63 32
    0b00000000000000000000000000000000#32)
  let w__411 ← (( do readReg PMCCFILTR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCCFILTR_EL0 (BitVec.update w__411 25 (Bit 0#1))
  let w__412 ← (( do readReg PMCCFILTR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCCFILTR_EL0 (Sail.BitVec.updateSubrange w__412 19 0 0b00000000000000000000#20)
  let w__413 ← (( do readReg ICC_NMIAR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_NMIAR1_EL1 (Sail.BitVec.updateSubrange w__413 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__414 ← (( do readReg DBGCLAIMSET_EL1 ) : SailM (BitVec 64) )
  writeReg DBGCLAIMSET_EL1 (Sail.BitVec.updateSubrange w__414 63 32
    0b00000000000000000000000000000000#32)
  let w__415 ← (( do readReg DBGCLAIMSET_EL1 ) : SailM (BitVec 64) )
  writeReg DBGCLAIMSET_EL1 (Sail.BitVec.updateSubrange w__415 31 8 0b000000000000000000000000#24)
  let w__416 ← (( do (ICC_SRE_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_SRE_EL1_write
    (Mk_ICC_SRE_EL1_Type
      (set_slice 61 w__416 3 0b0000000000000000000000000000000000000000000000000000000000000#61)))
  let w__417 ← (( do (ICC_SRE_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_SRE_EL1_write (_update_ICC_SRE_EL1_Type_DIB w__417 0#1))
  let w__418 ← (( do (ICC_SRE_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_SRE_EL1_write (_update_ICC_SRE_EL1_Type_DFB w__418 0#1))
  let w__419 ← (( do (ICC_SRE_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_SRE_EL1_write (_update_ICC_SRE_EL1_Type_SRE w__419 0#1))
  let w__420 ← (( do readReg ICC_IAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_IAR0_EL1 (Sail.BitVec.updateSubrange w__420 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__421 ← (( do readReg ESR_EL2 ) : SailM (BitVec 64) )
  writeReg ESR_EL2 (Sail.BitVec.updateSubrange w__421 63 56 0b00000000#8)
  let w__422 ← (( do readReg CONTEXTIDR_EL1 ) : SailM (BitVec 64) )
  writeReg CONTEXTIDR_EL1 (Sail.BitVec.updateSubrange w__422 63 32
    0b00000000000000000000000000000000#32)
  let w__423 ← (( do readReg ID_ISAR4_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR4_EL1 (Sail.BitVec.updateSubrange w__423 63 32
    0b00000000000000000000000000000000#32)
  let w__424 ← (( do readReg ID_ISAR4_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR4_EL1 (Sail.BitVec.updateSubrange w__424 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__425 ← (( do readReg ID_ISAR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR1_EL1 (Sail.BitVec.updateSubrange w__425 63 32
    0b00000000000000000000000000000000#32)
  let w__426 ← (( do readReg ID_ISAR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR1_EL1 (Sail.BitVec.updateSubrange w__426 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__427 ← (( do readReg PMUACR_EL1 ) : SailM (BitVec 64) )
  writeReg PMUACR_EL1 (Sail.BitVec.updateSubrange w__427 63 33 0b0000000000000000000000000000000#31)
  let w__428 ← (( do readReg DSPSR_EL0 ) : SailM (BitVec 64) )
  writeReg DSPSR_EL0 (Sail.BitVec.updateSubrange w__428 63 34 0b000000000000000000000000000000#30)
  let w__429 ← (( do readReg DSPSR_EL0 ) : SailM (BitVec 64) )
  writeReg DSPSR_EL0 (BitVec.update w__429 32 (Bit 0#1))
  let w__430 ← (( do readReg DSPSR_EL0 ) : SailM (BitVec 64) )
  writeReg DSPSR_EL0 (Sail.BitVec.updateSubrange w__430 63 35 0b00000000000000000000000000000#29)
  let w__431 ← (( do readReg DSPSR_EL0 ) : SailM (BitVec 64) )
  writeReg DSPSR_EL0 (Sail.BitVec.updateSubrange w__431 27 26 0b00#2)
  let w__432 ← (( do readReg DSPSR_EL0 ) : SailM (BitVec 64) )
  writeReg DSPSR_EL0 (Sail.BitVec.updateSubrange w__432 19 14 0b000000#6)
  let w__433 ← (( do readReg DSPSR_EL0 ) : SailM (BitVec 64) )
  writeReg DSPSR_EL0 (BitVec.update w__433 5 (Bit 0#1))
  let w__434 ← (( do readReg RMR_EL2 ) : SailM (BitVec 64) )
  writeReg RMR_EL2 (Sail.BitVec.updateSubrange w__434 63 2
    0b00000000000000000000000000000000000000000000000000000000000000#62)
  let w__435 ← (( do readReg RMR_EL2 ) : SailM (BitVec 64) )
  writeReg RMR_EL2 (Sail.BitVec.updateSubrange w__435 1 1 0#1)
  let w__436 ← (( do readReg VNCR_EL2 ) : SailM (BitVec 64) )
  writeReg VNCR_EL2 (Sail.BitVec.updateSubrange w__436 11 0 0b000000000000#12)
  let w__437 ← (( do readReg PMINTENCLR_EL1 ) : SailM (BitVec 64) )
  writeReg PMINTENCLR_EL1 (Sail.BitVec.updateSubrange w__437 63 33
    0b0000000000000000000000000000000#31)
  let w__438 ← (( do readReg PMINTENCLR_EL1 ) : SailM (BitVec 64) )
  writeReg PMINTENCLR_EL1 (BitVec.update w__438 32 (Bit 0#1))
  let w__439 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
  writeReg PMSELR_EL0 (Sail.BitVec.updateSubrange w__439 63 5
    0b00000000000000000000000000000000000000000000000000000000000#59)
  let w__440 ← (( do (ICC_CTLR_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_CTLR_EL1_write
    (Mk_ICC_CTLR_EL1_Type (set_slice 44 w__440 20 0b00000000000000000000000000000000000000000000#44)))
  let w__441 ← (( do (ICC_CTLR_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_CTLR_EL1_write (Mk_ICC_CTLR_EL1_Type (set_slice 2 w__441 16 0b00#2)))
  let w__442 ← (( do (ICC_CTLR_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_CTLR_EL1_write (Mk_ICC_CTLR_EL1_Type (set_slice 1 w__442 7 0#1)))
  let w__443 ← (( do (ICC_CTLR_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_CTLR_EL1_write (Mk_ICC_CTLR_EL1_Type (set_slice 4 w__443 2 0b0000#4)))
  let w__444 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange w__444 63 32
    0b00000000000000000000000000000000#32)
  let w__445 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange w__445 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__446 ← (( do readReg CNTP_CTL_EL0 ) : SailM (BitVec 64) )
  writeReg CNTP_CTL_EL0 (Sail.BitVec.updateSubrange w__446 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  let w__447 ← (( do readReg HFGITR2_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR2_EL2 (Sail.BitVec.updateSubrange w__447 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__448 ← (( do readReg CNTHV_TVAL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHV_TVAL_EL2 (Sail.BitVec.updateSubrange w__448 63 32
    0b00000000000000000000000000000000#32)
  let w__449 ← (( do readReg SPSR_irq ) : SailM (BitVec 64) )
  writeReg SPSR_irq (Sail.BitVec.updateSubrange w__449 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__450 ← (( do readReg SPSR_irq ) : SailM (BitVec 64) )
  writeReg SPSR_irq (Sail.BitVec.updateSubrange w__450 63 32 0b00000000000000000000000000000000#32)
  let w__451 ← (( do readReg ICH_MISR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_MISR_EL2 (Sail.BitVec.updateSubrange w__451 63 8
    0b00000000000000000000000000000000000000000000000000000000#56)
  let w__452 ← (( do readReg ICH_MISR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_MISR_EL2 (Sail.BitVec.updateSubrange w__452 7 7 0#1)
  let w__453 ← (( do readReg ICH_MISR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_MISR_EL2 (Sail.BitVec.updateSubrange w__453 6 6 0#1)
  let w__454 ← (( do readReg ICH_MISR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_MISR_EL2 (Sail.BitVec.updateSubrange w__454 5 5 0#1)
  let w__455 ← (( do readReg ICH_MISR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_MISR_EL2 (Sail.BitVec.updateSubrange w__455 4 4 0#1)
  let w__456 ← (( do readReg ICH_MISR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_MISR_EL2 (Sail.BitVec.updateSubrange w__456 3 3 0#1)
  let w__457 ← (( do readReg ICH_MISR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_MISR_EL2 (Sail.BitVec.updateSubrange w__457 2 2 0#1)
  let w__458 ← (( do readReg ICH_MISR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_MISR_EL2 (Sail.BitVec.updateSubrange w__458 1 1 0#1)
  let w__459 ← (( do readReg ICH_MISR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_MISR_EL2 (Sail.BitVec.updateSubrange w__459 0 0 0#1)
  let w__460 ← (( do readReg CSSELR_EL1 ) : SailM (BitVec 64) )
  writeReg CSSELR_EL1 (Sail.BitVec.updateSubrange w__460 63 5
    0b00000000000000000000000000000000000000000000000000000000000#59)
  let w__461 ← (( do readReg ICV_RPR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_RPR_EL1 (Sail.BitVec.updateSubrange w__461 62 8
    0b0000000000000000000000000000000000000000000000000000000#55)
  let w__462 ← (( do readReg PFAR_EL2 ) : SailM (BitVec 64) )
  writeReg PFAR_EL2 (Sail.BitVec.updateSubrange w__462 61 56 0b000000#6)
  let w__463 ← (( do readReg ICV_PMR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_PMR_EL1 (Sail.BitVec.updateSubrange w__463 63 8
    0b00000000000000000000000000000000000000000000000000000000#56)
  let w__464 ← (( do readReg MFAR_EL3 ) : SailM (BitVec 64) )
  writeReg MFAR_EL3 (Sail.BitVec.updateSubrange w__464 61 56 0b000000#6)
  let w__465 ← (( do readReg MFAR_EL3 ) : SailM (BitVec 64) )
  writeReg MFAR_EL3 (Sail.BitVec.updateSubrange w__465 11 0 0b000000000000#12)
  let w__466 ← (( do readReg MFAR_EL3 ) : SailM (BitVec 64) )
  writeReg MFAR_EL3 (Sail.BitVec.updateSubrange w__466 61 56 0b000000#6)
  let w__467 ← (( do readReg SPSR_EL2 ) : SailM (BitVec 64) )
  writeReg SPSR_EL2 (Sail.BitVec.updateSubrange w__467 63 34 0b000000000000000000000000000000#30)
  let w__468 ← (( do readReg SPSR_EL2 ) : SailM (BitVec 64) )
  writeReg SPSR_EL2 (BitVec.update w__468 32 (Bit 0#1))
  let w__469 ← (( do readReg SPSR_EL2 ) : SailM (BitVec 64) )
  writeReg SPSR_EL2 (Sail.BitVec.updateSubrange w__469 63 35 0b00000000000000000000000000000#29)
  let w__470 ← (( do readReg SPSR_EL2 ) : SailM (BitVec 64) )
  writeReg SPSR_EL2 (Sail.BitVec.updateSubrange w__470 27 26 0b00#2)
  let w__471 ← (( do readReg SPSR_EL2 ) : SailM (BitVec 64) )
  writeReg SPSR_EL2 (Sail.BitVec.updateSubrange w__471 19 14 0b000000#6)
  let w__472 ← (( do readReg SPSR_EL2 ) : SailM (BitVec 64) )
  writeReg SPSR_EL2 (BitVec.update w__472 5 (Bit 0#1))
  let w__473 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
  writeReg TCR_EL1 (Sail.BitVec.updateSubrange w__473 63 62 0b00#2)
  let w__474 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
  writeReg TCR_EL1 (BitVec.update w__474 35 (Bit 0#1))
  let w__475 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
  writeReg TCR_EL1 (BitVec.update w__475 6 (Bit 0#1))
  let w__476 ← (( do readReg ICV_HPPIR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_HPPIR0_EL1 (Sail.BitVec.updateSubrange w__476 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__477 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
  writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__477 63 7
    0b000000000000000000000000000000000000000000000000000000000#57)
  let w__481 ← (( do
    if ((← do
         if (((! cold) : Bool) : Bool)
         then
           (do
             let w__478 ← (( do (HaveEL EL2) ) : SailM Bool )
             (pure (((! w__478) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__480 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__480) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__481 : Bool)
  then
    (do
      let w__482 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
      writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__482 6 6 0#1))
  else
    (do
      let w__483 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
      let w__484 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__483 6 6 w__484))
  let w__488 ← (( do
    if ((← do
         if (((! cold) : Bool) : Bool)
         then
           (do
             let w__485 ← (( do (HaveEL EL2) ) : SailM Bool )
             (pure (((! w__485) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__487 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__487) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__488 : Bool)
  then
    (do
      let w__489 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
      writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__489 5 5 0#1))
  else
    (do
      let w__490 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
      let w__491 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__490 5 5 w__491))
  let w__495 ← (( do
    if ((← do
         if (((! cold) : Bool) : Bool)
         then
           (do
             let w__492 ← (( do (HaveEL EL2) ) : SailM Bool )
             (pure (((! w__492) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__494 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__494) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__495 : Bool)
  then
    (do
      let w__496 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
      writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__496 4 4 0#1))
  else
    (do
      let w__497 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
      let w__498 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__497 4 4 w__498))
  let w__502 ← (( do
    if ((← do
         if (((! cold) : Bool) : Bool)
         then
           (do
             let w__499 ← (( do (HaveEL EL2) ) : SailM Bool )
             (pure (((! w__499) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__501 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__501) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__502 : Bool)
  then
    (do
      let w__503 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
      writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__503 3 3 0#1))
  else
    (do
      let w__504 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
      let w__505 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__504 3 3 w__505))
  let w__509 ← (( do
    if ((← do
         if (((! cold) : Bool) : Bool)
         then
           (do
             let w__506 ← (( do (HaveEL EL2) ) : SailM Bool )
             (pure (((! w__506) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__508 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__508) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__509 : Bool)
  then
    (do
      let w__510 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
      writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__510 2 2 0#1))
  else
    (do
      let w__511 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
      let w__512 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__511 2 2 w__512))
  let w__513 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
  writeReg SCTLR2_EL1 (Sail.BitVec.updateSubrange w__513 1 0 0b00#2)
  let w__514 ← (( do readReg ICV_BPR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_BPR0_EL1 (Sail.BitVec.updateSubrange w__514 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  let w__515 ← (( do readReg ISR_EL1 ) : SailM (BitVec 64) )
  writeReg ISR_EL1 (Sail.BitVec.updateSubrange w__515 63 11
    0b00000000000000000000000000000000000000000000000000000#53)
  let w__516 ← (( do readReg ISR_EL1 ) : SailM (BitVec 64) )
  writeReg ISR_EL1 (Sail.BitVec.updateSubrange w__516 5 0 0b000000#6)
  let w__517 ← (( do readReg ID_ISAR3_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR3_EL1 (Sail.BitVec.updateSubrange w__517 63 32
    0b00000000000000000000000000000000#32)
  let w__518 ← (( do readReg ID_ISAR3_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR3_EL1 (Sail.BitVec.updateSubrange w__518 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__519 ← (( do readReg MECIDR_EL2 ) : SailM (BitVec 64) )
  writeReg MECIDR_EL2 (Sail.BitVec.updateSubrange w__519 63 4
    0b000000000000000000000000000000000000000000000000000000000000#60)
  let w__520 ← (( do readReg PMINTENSET_EL1 ) : SailM (BitVec 64) )
  writeReg PMINTENSET_EL1 (Sail.BitVec.updateSubrange w__520 63 33
    0b0000000000000000000000000000000#31)
  let w__521 ← (( do readReg PMINTENSET_EL1 ) : SailM (BitVec 64) )
  writeReg PMINTENSET_EL1 (BitVec.update w__521 32 (Bit 0#1))
  let w__522 ← (( do readReg SMIDR_EL1 ) : SailM (BitVec 64) )
  writeReg SMIDR_EL1 (Sail.BitVec.updateSubrange w__522 63 32 0b00000000000000000000000000000000#32)
  let w__523 ← (( do readReg SMIDR_EL1 ) : SailM (BitVec 64) )
  writeReg SMIDR_EL1 (Sail.BitVec.updateSubrange w__523 14 12 0b000#3)
  let w__524 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__524 63 63 0#1)
  let w__525 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__525 62 62 0#1)
  let w__526 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__526 61 61 0#1)
  let w__527 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__527 60 60 0#1)
  let w__528 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__528 59 59 0#1)
  let w__529 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__529 58 58 0#1)
  let w__530 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__530 57 57 0#1)
  let w__531 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__531 56 56 0#1)
  let w__532 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__532 55 55 0#1)
  let w__533 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__533 54 54 0#1)
  let w__534 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__534 53 53 0#1)
  let w__535 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__535 52 52 0#1)
  let w__536 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (BitVec.update w__536 51 (Bit 0#1))
  let w__537 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__537 50 50 0#1)
  let w__539 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__538 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__538) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__539 : Bool)
  then
    (do
      let w__540 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__540 49 49 0#1))
  else
    (do
      let w__541 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      let w__542 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__541 49 49 w__542))
  let w__544 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__543 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__543) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__544 : Bool)
  then
    (do
      let w__545 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__545 48 48 0#1))
  else
    (do
      let w__546 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      let w__547 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__546 48 48 w__547))
  let w__549 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__548 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__548) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__549 : Bool)
  then
    (do
      let w__550 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__550 47 47 0#1))
  else
    (do
      let w__551 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      let w__552 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__551 47 47 w__552))
  let w__553 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (BitVec.update w__553 46 (Bit 0#1))
  let w__555 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__554 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__554) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__555 : Bool)
  then
    (do
      let w__556 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__556 45 45 0#1))
  else
    (do
      let w__557 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      let w__558 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__557 45 45 w__558))
  let w__560 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__559 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__559) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__560 : Bool)
  then
    (do
      let w__561 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__561 44 44 0#1))
  else
    (do
      let w__562 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      let w__563 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__562 44 44 w__563))
  let w__565 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__564 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__564) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__565 : Bool)
  then
    (do
      let w__566 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__566 43 43 0#1))
  else
    (do
      let w__567 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      let w__568 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__567 43 43 w__568))
  let w__569 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (BitVec.update w__569 42 (Bit 0#1))
  let w__571 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__570 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__570) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__571 : Bool)
  then
    (do
      let w__572 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__572 41 41 0#1))
  else
    (do
      let w__573 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
      let w__574 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__573 41 41 w__574))
  let w__575 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (BitVec.update w__575 40 (Bit 0#1))
  let w__576 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__576 39 39 0#1)
  let w__577 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__577 38 38 0#1)
  let w__578 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__578 37 37 0#1)
  let w__579 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__579 36 36 0#1)
  let w__580 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__580 35 35 0#1)
  let w__581 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__581 34 34 0#1)
  let w__582 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__582 33 33 0#1)
  let w__583 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__583 32 32 0#1)
  let w__584 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__584 31 31 0#1)
  let w__585 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__585 30 30 0#1)
  let w__586 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__586 29 29 0#1)
  let w__587 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (BitVec.update w__587 28 (Bit 0#1))
  let w__588 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__588 27 27 0#1)
  let w__589 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__589 26 25 0b00#2)
  let w__590 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__590 24 24 0#1)
  let w__591 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__591 23 23 0#1)
  let w__592 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__592 22 22 0#1)
  let w__593 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (BitVec.update w__593 21 (Bit 0#1))
  let w__594 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__594 20 20 0#1)
  let w__595 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__595 19 19 0#1)
  let w__596 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (BitVec.update w__596 18 (Bit 0#1))
  let w__597 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__597 17 17 0#1)
  let w__598 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__598 16 16 0#1)
  let w__599 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__599 15 14 0b00#2)
  let w__600 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__600 13 13 0#1)
  let w__601 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__601 12 12 0#1)
  let w__602 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__602 11 11 0#1)
  let w__603 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__603 10 9 0b00#2)
  let w__604 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__604 8 8 0#1)
  let w__605 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__605 7 7 0#1)
  let w__606 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__606 6 6 0#1)
  let w__607 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__607 5 5 0#1)
  let w__608 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__608 4 4 0#1)
  let w__609 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__609 3 3 0#1)
  let w__610 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (BitVec.update w__610 2 (Bit 0#1))
  let w__611 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__611 1 1 0#1)
  let w__612 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR_EL2 (Sail.BitVec.updateSubrange w__612 0 0 0#1)
  let w__613 ← (( do readReg SMPRI_EL1 ) : SailM (BitVec 64) )
  writeReg SMPRI_EL1 (Sail.BitVec.updateSubrange w__613 63 4
    0b000000000000000000000000000000000000000000000000000000000000#60)
  let w__614 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
  writeReg PMUSERENR_EL0 (Sail.BitVec.updateSubrange w__614 63 7
    0b000000000000000000000000000000000000000000000000000000000#57)
  let w__615 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__615 63 7
    0b000000000000000000000000000000000000000000000000000000000#57)
  let w__617 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__616 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__616) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__617 : Bool)
  then
    (do
      let w__618 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__618 6 6 0#1))
  else
    (do
      let w__619 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      let w__620 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__619 6 6 w__620))
  let w__622 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__621 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__621) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__622 : Bool)
  then
    (do
      let w__623 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__623 5 5 0#1))
  else
    (do
      let w__624 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      let w__625 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__624 5 5 w__625))
  let w__627 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__626 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__626) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__627 : Bool)
  then
    (do
      let w__628 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__628 4 4 0#1))
  else
    (do
      let w__629 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      let w__630 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__629 4 4 w__630))
  let w__632 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__631 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__631) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__632 : Bool)
  then
    (do
      let w__633 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__633 3 3 0#1))
  else
    (do
      let w__634 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      let w__635 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__634 3 3 w__635))
  let w__637 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__636 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__636) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__637 : Bool)
  then
    (do
      let w__638 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__638 2 2 0#1))
  else
    (do
      let w__639 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      let w__640 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__639 2 2 w__640))
  let w__642 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__641 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__641) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__642 : Bool)
  then
    (do
      let w__643 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__643 1 1 0#1))
  else
    (do
      let w__644 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
      let w__645 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR2_EL2 (Sail.BitVec.updateSubrange w__644 1 1 w__645))
  let w__646 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR2_EL2 (BitVec.update w__646 0 (Bit 0#1))
  let w__647 ← (( do readReg PMOVSSET_EL0 ) : SailM (BitVec 64) )
  writeReg PMOVSSET_EL0 (Sail.BitVec.updateSubrange w__647 63 33
    0b0000000000000000000000000000000#31)
  let w__648 ← (( do readReg PMOVSSET_EL0 ) : SailM (BitVec 64) )
  writeReg PMOVSSET_EL0 (BitVec.update w__648 32 (Bit 0#1))
  let w__649 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (BitVec.update w__649 63 (Bit 0#1))
  let w__650 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__650 61 61 0#1)
  let w__651 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (BitVec.update w__651 60 (Bit 0#1))
  let w__652 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__652 58 54 0b00000#5)
  let w__653 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (BitVec.update w__653 52 (Bit 0#1))
  let w__654 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__654 50 45 0b000000#6)
  let w__655 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (BitVec.update w__655 42 (Bit 0#1))
  let w__656 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__656 39 38 0b00#2)
  let w__657 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__657 35 32 0b0000#4)
  let w__658 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__658 29 28 0b11#2)
  let w__659 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (BitVec.update w__659 26 (Bit 0#1))
  let w__660 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (BitVec.update w__660 24 (Bit 0#1))
  let w__661 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (BitVec.update w__661 23 (Bit 1#1))
  let w__662 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (BitVec.update w__662 20 (Bit 0#1))
  let w__663 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (BitVec.update w__663 18 (Bit 1#1))
  let w__664 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (BitVec.update w__664 17 (Bit 0#1))
  let w__665 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (BitVec.update w__665 16 (Bit 1#1))
  let w__666 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__666 15 14 0b00#2)
  let w__667 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__667 12 12 0#1)
  let w__668 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__668 10 7 0b0000#4)
  let w__669 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__669 5 4 0b11#2)
  let w__670 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__670 2 2 0#1)
  let w__671 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__671 0 0 0#1)
  let w__672 ← (( do readReg VBAR_EL1 ) : SailM (BitVec 64) )
  writeReg VBAR_EL1 (Sail.BitVec.updateSubrange w__672 10 0 0b00000000000#11)
  let w__673 ← (( do readReg CNTFRQ_EL0 ) : SailM (BitVec 64) )
  writeReg CNTFRQ_EL0 (Sail.BitVec.updateSubrange w__673 63 32 0b00000000000000000000000000000000#32)
  let w__674 ← (( do readReg ICV_CTLR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange w__674 63 20
    0b00000000000000000000000000000000000000000000#44)
  let w__675 ← (( do readReg ICV_CTLR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange w__675 17 16 0b00#2)
  let w__676 ← (( do readReg ICV_CTLR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange w__676 7 2 0b000000#6)
  let w__677 ← (( do readReg MECID_A0_EL2 ) : SailM (BitVec 64) )
  writeReg MECID_A0_EL2 (Sail.BitVec.updateSubrange w__677 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__678 ← (( do readReg ICV_IAR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_IAR1_EL1 (Sail.BitVec.updateSubrange w__678 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__679 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
  writeReg CPACR_EL1 (Sail.BitVec.updateSubrange w__679 63 30
    0b0000000000000000000000000000000000#34)
  let w__680 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
  writeReg CPACR_EL1 (Sail.BitVec.updateSubrange w__680 27 26 0b00#2)
  let w__681 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
  writeReg CPACR_EL1 (Sail.BitVec.updateSubrange w__681 23 22 0b00#2)
  let w__682 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
  writeReg CPACR_EL1 (Sail.BitVec.updateSubrange w__682 19 18 0b00#2)
  let w__683 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
  writeReg CPACR_EL1 (Sail.BitVec.updateSubrange w__683 15 0 0b0000000000000000#16)
  let w__684 ← (( do readReg DBGDTRRX_EL0 ) : SailM (BitVec 64) )
  writeReg DBGDTRRX_EL0 (Sail.BitVec.updateSubrange w__684 63 32
    0b00000000000000000000000000000000#32)
  let w__685 ← (( do readReg SPSR_EL1 ) : SailM (BitVec 64) )
  writeReg SPSR_EL1 (Sail.BitVec.updateSubrange w__685 63 34 0b000000000000000000000000000000#30)
  let w__686 ← (( do readReg SPSR_EL1 ) : SailM (BitVec 64) )
  writeReg SPSR_EL1 (BitVec.update w__686 32 (Bit 0#1))
  let w__687 ← (( do readReg SPSR_EL1 ) : SailM (BitVec 64) )
  writeReg SPSR_EL1 (Sail.BitVec.updateSubrange w__687 63 35 0b00000000000000000000000000000#29)
  let w__688 ← (( do readReg SPSR_EL1 ) : SailM (BitVec 64) )
  writeReg SPSR_EL1 (Sail.BitVec.updateSubrange w__688 27 26 0b00#2)
  let w__689 ← (( do readReg SPSR_EL1 ) : SailM (BitVec 64) )
  writeReg SPSR_EL1 (Sail.BitVec.updateSubrange w__689 19 14 0b000000#6)
  let w__690 ← (( do readReg SPSR_EL1 ) : SailM (BitVec 64) )
  writeReg SPSR_EL1 (BitVec.update w__690 5 (Bit 0#1))
  let w__691 ← (( do readReg FPEXC32_EL2 ) : SailM (BitVec 64) )
  writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange w__691 63 32
    0b00000000000000000000000000000000#32)
  let w__692 ← (( do readReg FPEXC32_EL2 ) : SailM (BitVec 64) )
  writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange w__692 25 11 0b000000000000000#15)
  let w__693 ← (( do readReg FPEXC32_EL2 ) : SailM (BitVec 64) )
  writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange w__693 6 5 0b00#2)
  let w__694 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__694 63 36 0b0000000000000000000000000000#28)
  if (cold : Bool)
  then
    (do
      let w__695 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
      writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__695 35 35 0#1))
  else (pure (()))
  let w__696 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (BitVec.update w__696 33 (Bit 0#1))
  let w__700 ← (( do
    if ((← do
         if (((! cold) : Bool) : Bool)
         then
           (do
             let w__697 ← (( do (HaveEL EL2) ) : SailM Bool )
             (pure (((! w__697) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__699 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__699) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__700 : Bool)
  then
    (do
      let w__701 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
      writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__701 32 32 0#1))
  else
    (do
      let w__702 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
      let w__703 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__702 32 32 w__703))
  let w__704 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (BitVec.update w__704 28 (Bit 0#1))
  let w__705 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__705 25 24 0b00#2)
  let w__706 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (BitVec.update w__706 20 (Bit 0#1))
  let w__707 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__707 18 16 0b000#3)
  let w__708 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__708 11 7 0b00000#5)
  let w__709 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__709 5 1 0b00000#5)
  let w__710 ← (( do readReg SPSR_fiq ) : SailM (BitVec 64) )
  writeReg SPSR_fiq (Sail.BitVec.updateSubrange w__710 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__711 ← (( do readReg SPSR_fiq ) : SailM (BitVec 64) )
  writeReg SPSR_fiq (Sail.BitVec.updateSubrange w__711 63 32 0b00000000000000000000000000000000#32)
  let w__712 ← (( do readReg MECID_P0_EL2 ) : SailM (BitVec 64) )
  writeReg MECID_P0_EL2 (Sail.BitVec.updateSubrange w__712 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__713 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
  writeReg GPCCR_EL3 (Sail.BitVec.updateSubrange w__713 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__714 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
  writeReg GPCCR_EL3 (Sail.BitVec.updateSubrange w__714 19 18 0b00#2)
  let w__715 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
  writeReg GPCCR_EL3 (Sail.BitVec.updateSubrange w__715 16 16 0#1)
  let w__716 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
  writeReg GPCCR_EL3 (Sail.BitVec.updateSubrange w__716 7 3 0b00000#5)
  let w__717 ← (( do readReg ID_PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR0_EL1 (Sail.BitVec.updateSubrange w__717 63 32
    0b00000000000000000000000000000000#32)
  let w__718 ← (( do readReg ID_PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR0_EL1 (Sail.BitVec.updateSubrange w__718 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__719 ← (( do readReg MVFR1_EL1 ) : SailM (BitVec 64) )
  writeReg MVFR1_EL1 (Sail.BitVec.updateSubrange w__719 63 32 0b00000000000000000000000000000000#32)
  (pure true)


end ArmFull.Functions
