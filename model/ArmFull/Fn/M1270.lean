import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0933
import ArmFull.Fn.M1016
import ArmFull.Fn.M1017
import ArmFull.Fn.M1107
import ArmFull.Fn.M1108
import ArmFull.Fn.M1152

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

/-- Type quantifiers: pc : Int -/
def __DecodeA64_DataProcFPSIMD__seg8 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__625 ← (( do
    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
             __opcode 29 10)) == (0x3BE62#20 : (BitVec 20)))) : Bool) : Bool)
    then
      (do
        let w__624 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__624 <b 450) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__625 : Bool)
  then
    (do
      writeReg SEE 450
      let Rd := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let o1 := (BitVec.slice __opcode 12 1)
      let o2 := (BitVec.slice __opcode 23 1)
      let U := (BitVec.slice __opcode 29 1)
      let Q := (BitVec.slice __opcode 30 1)
      (decode_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U Q)
      (pure false))
  else
    (do
      let w__627 ← (( do
        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                   __opcode 29 23)) == (0b0011101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                   __opcode 21 10)) == (0x862#12 : (BitVec 12))))) : Bool) : Bool)
        then
          (do
            let w__626 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__626 <b 451) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__627 : Bool)
      then
        (do
          writeReg SEE 451
          let Rd := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let o1 := (BitVec.slice __opcode 12 1)
          let sz := (BitVec.slice __opcode 22 1)
          let o2 := (BitVec.slice __opcode 23 1)
          let U := (BitVec.slice __opcode 29 1)
          let Q := (BitVec.slice __opcode 30 1)
          (decode_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1 sz o2 U
            Q)
          (pure false))
      else
        (do
          let w__629 ← (( do
            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                     __opcode 29 10)) == (0xB9E66#20 : (BitVec 20)))) : Bool) : Bool)
            then
              (do
                let w__628 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__628 <b 452) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__629 : Bool)
          then
            (do
              writeReg SEE 452
              let Rd := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let o1 := (BitVec.slice __opcode 12 1)
              let o2 := (BitVec.slice __opcode 23 1)
              let U := (BitVec.slice __opcode 29 1)
              let Q := (BitVec.slice __opcode 30 1)
              (decode_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn o1 o2 U
                Q)
              (pure false))
          else
            (do
              let w__631 ← (( do
                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                           __opcode 29 23)) == (0b1011100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                           __opcode 21 10)) == (0x866#12 : (BitVec 12))))) : Bool) : Bool)
                then
                  (do
                    let w__630 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__630 <b 453) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__631 : Bool)
              then
                (do
                  writeReg SEE 453
                  let Rd := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let o1 := (BitVec.slice __opcode 12 1)
                  let sz := (BitVec.slice __opcode 22 1)
                  let o2 := (BitVec.slice __opcode 23 1)
                  let U := (BitVec.slice __opcode 29 1)
                  let Q := (BitVec.slice __opcode 30 1)
                  (decode_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round Rd Rn o1
                    sz o2 U Q)
                  (pure false))
              else
                (do
                  let w__633 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                             __opcode 29 10)) == (0x3BE66#20 : (BitVec 20)))) : Bool) : Bool)
                    then
                      (do
                        let w__632 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__632 <b 454) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__633 : Bool)
                  then
                    (do
                      writeReg SEE 454
                      let Rd := (BitVec.slice __opcode 0 5)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let o1 := (BitVec.slice __opcode 12 1)
                      let o2 := (BitVec.slice __opcode 23 1)
                      let U := (BitVec.slice __opcode 29 1)
                      let Q := (BitVec.slice __opcode 30 1)
                      (decode_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round Rd Rn
                        o1 o2 U Q)
                      (pure false))
                  else
                    (do
                      let w__635 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31
                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                   __opcode 29 23)) == (0b0011101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                   __opcode 21 10)) == (0x866#12 : (BitVec 12))))) : Bool) : Bool)
                        then
                          (do
                            let w__634 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__634 <b 455) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__635 : Bool)
                      then
                        (do
                          writeReg SEE 455
                          let Rd := (BitVec.slice __opcode 0 5)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let o1 := (BitVec.slice __opcode 12 1)
                          let sz := (BitVec.slice __opcode 22 1)
                          let o2 := (BitVec.slice __opcode 23 1)
                          let U := (BitVec.slice __opcode 29 1)
                          let Q := (BitVec.slice __opcode 30 1)
                          (decode_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round
                            Rd Rn o1 sz o2 U Q)
                          (pure false))
                      else
                        (do
                          let w__637 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode
                                     31 24)) == (0x1E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                     __opcode 21 10)) == (0x990#12 : (BitVec 12)))) : Bool) : Bool)
                            then
                              (do
                                let w__636 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__636 <b 456) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__637 : Bool)
                          then
                            (do
                              writeReg SEE 456
                              let Rd := (BitVec.slice __opcode 0 5)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let rmode := (BitVec.slice __opcode 15 3)
                              let ftype := (BitVec.slice __opcode 22 2)
                              (decode_frinta_float_aarch64_instrs_float_arithmetic_round_frint Rd Rn
                                rmode ftype)
                              (pure false))
                          else
                            (do
                              let w__639 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                         __opcode 31 24)) == (0x1E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                         __opcode 21 10)) == (0x9F0#12 : (BitVec 12)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__638 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__638 <b 457) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__639 : Bool)
                              then
                                (do
                                  writeReg SEE 457
                                  let Rd := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let rmode := (BitVec.slice __opcode 15 3)
                                  let ftype := (BitVec.slice __opcode 22 2)
                                  (decode_frinti_float_aarch64_instrs_float_arithmetic_round_frint
                                    Rd Rn rmode ftype)
                                  (pure false))
                              else
                                (do
                                  let w__641 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                             __opcode 31 24)) == (0x1E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                             __opcode 21 10)) == (0x950#12 : (BitVec 12)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__640 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__640 <b 458) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__641 : Bool)
                                  then
                                    (do
                                      writeReg SEE 458
                                      let Rd := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let rmode := (BitVec.slice __opcode 15 3)
                                      let ftype := (BitVec.slice __opcode 22 2)
                                      (decode_frintm_float_aarch64_instrs_float_arithmetic_round_frint
                                        Rd Rn rmode ftype)
                                      (pure false))
                                  else
                                    (do
                                      let w__643 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                 __opcode 31 24)) == (0x1E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                 __opcode 21 10)) == (0x910#12 : (BitVec 12)))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__642 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__642 <b 459) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__643 : Bool)
                                      then
                                        (do
                                          writeReg SEE 459
                                          let Rd := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let rmode := (BitVec.slice __opcode 15 3)
                                          let ftype := (BitVec.slice __opcode 22 2)
                                          (decode_frintn_float_aarch64_instrs_float_arithmetic_round_frint
                                            Rd Rn rmode ftype)
                                          (pure false))
                                      else
                                        (do
                                          let w__645 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                     __opcode 31 24)) == (0x1E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                     __opcode 21 10)) == (0x930#12 : (BitVec 12)))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__644 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__644 <b 460) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__645 : Bool)
                                          then
                                            (do
                                              writeReg SEE 460
                                              let Rd := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let rmode := (BitVec.slice __opcode 15 3)
                                              let ftype := (BitVec.slice __opcode 22 2)
                                              (decode_frintp_float_aarch64_instrs_float_arithmetic_round_frint
                                                Rd Rn rmode ftype)
                                              (pure false))
                                          else
                                            (do
                                              let w__647 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                         __opcode 31 24)) == (0x1E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                         __opcode 21 10)) == (0x9D0#12 : (BitVec 12)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__646 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__646 <b 461) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__647 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 461
                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let rmode := (BitVec.slice __opcode 15 3)
                                                  let ftype := (BitVec.slice __opcode 22 2)
                                                  (decode_frintx_float_aarch64_instrs_float_arithmetic_round_frint
                                                    Rd Rn rmode ftype)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__649 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                             __opcode 31 24)) == (0x1E#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                             __opcode 21 10)) == (0x970#12 : (BitVec 12)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__648 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__648 <b 462) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__649 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 462
                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let rmode := (BitVec.slice __opcode 15 3)
                                                      let ftype := (BitVec.slice __opcode 22 2)
                                                      (decode_frintz_float_aarch64_instrs_float_arithmetic_round_frint
                                                        Rd Rn rmode ftype)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__651 ← (( do
                                                        if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                               __opcode 31 10)) == (0b0111111011111001110110#22 : (BitVec 22))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__650 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__650 <b 463) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__651 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 463
                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          (decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd
                                                            Rd Rn)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__653 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                     __opcode 31 23)) == (0b011111101#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                     __opcode 21 10)) == (0x876#12 : (BitVec 12)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__652 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__652 <b 464) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__653 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 464
                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let sz := (BitVec.slice __opcode 22 1)
                                                              (decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_float_sisd
                                                                Rd Rn sz)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__655 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 31 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                         __opcode 29 10)) == (0xBBE76#20 : (BitVec 20)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__654 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__654 <b 465) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__655 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 465
                                                                  let Rd :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let Q :=
                                                                    (BitVec.slice __opcode 30 1)
                                                                  (decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_simd
                                                                    Rd Rn Q)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__657 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                               __opcode 29 23)) == (0b1011101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                               __opcode 21 10)) == (0x876#12 : (BitVec 12))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__656 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__656 <b 466) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__657 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 466
                                                                      let Rd :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let sz :=
                                                                        (BitVec.slice __opcode 22 1)
                                                                      let Q :=
                                                                        (BitVec.slice __opcode 30 1)
                                                                      (decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_float_simd
                                                                        Rd Rn sz Q)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__659 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 21)) == (0b01011110110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                 __opcode 15 10)) == (0b001111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__658 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__658 <b 467) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__659 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 467
                                                                          let Rd :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let Rm :=
                                                                            (BitVec.slice __opcode
                                                                              16 5)
                                                                          (decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd
                                                                            Rd Rn Rm)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__661 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 23)) == (0b010111101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                       __opcode 15
                                                                                       10)) == (0b111111#6 : (BitVec 6))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__660 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__660 <b 468) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__661 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 468
                                                                              let Rd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let Rm :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 5)
                                                                              let sz :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              (decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_sisd
                                                                                Rd Rn Rm sz)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__663 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           29 21)) == (0b001110110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           15 10)) == (0b001111#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__662 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__662 <b 469) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__663 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 469
                                                                                  let Rd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let Rm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 5)
                                                                                  let Q :=
                                                                                    (BitVec.slice
                                                                                      __opcode 30 1)
                                                                                  (decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_simd
                                                                                    Rd Rn Rm Q)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__665 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               29 23)) == (0b0011101#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 21
                                                                                                 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 15
                                                                                                 10)) == (0b111111#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__664 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__664 <b 470) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__665 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 470
                                                                                      let Rd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let Rm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 5)
                                                                                      let sz :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 1)
                                                                                      let Q :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          30 1)
                                                                                      (decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_simd
                                                                                        Rd Rn Rm sz
                                                                                        Q)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__667 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 29
                                                                                                 10)) == (0xBBE7E#20 : (BitVec 20)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__666 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__666 <b 471) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__667 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 471
                                                                                          let Rd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let Q :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              30 1)
                                                                                          (decode_fsqrt_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_fp16
                                                                                            Rd Rn Q)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__669 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       29
                                                                                                       23)) == (0b1011101#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       10)) == (0x87E#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__668 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__668 <b 472) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__669 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 472
                                                                                              let Rd :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  5)
                                                                                              let Rn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  5)
                                                                                              let sz :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  1)
                                                                                              let Q :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  30
                                                                                                  1)
                                                                                              (decode_fsqrt_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt
                                                                                                Rd
                                                                                                Rn
                                                                                                sz Q)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__671 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           29
                                                                                                           21)) == (0b001110110#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           15
                                                                                                           10)) == (0b000101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__670 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__670 <b 473) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__671 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 473
                                                                                                  let Rd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      5)
                                                                                                  let Rn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      5)
                                                                                                  let Rm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      5)
                                                                                                  let U :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      29
                                                                                                      1)
                                                                                                  let Q :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      30
                                                                                                      1)
                                                                                                  (decode_fsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd
                                                                                                    Rd
                                                                                                    Rn
                                                                                                    Rm
                                                                                                    U
                                                                                                    Q)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__673 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               29
                                                                                                               23)) == (0b0011101#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 21
                                                                                                                 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 15
                                                                                                                 10)) == (0b110101#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__672 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__672 <b 474) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__673 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 474
                                                                                                      let Rd :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          5)
                                                                                                      let Rn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          5)
                                                                                                      let Rm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          5)
                                                                                                      let sz :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          1)
                                                                                                      let U :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          29
                                                                                                          1)
                                                                                                      let Q :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          30
                                                                                                          1)
                                                                                                      (decode_fsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_simd
                                                                                                        Rd
                                                                                                        Rn
                                                                                                        Rm
                                                                                                        sz
                                                                                                        U
                                                                                                        Q)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__675 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 21)) == (0b01101110000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   15
                                                                                                                   15)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   10
                                                                                                                   10)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__674 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__674 <b 480) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__675 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 480
                                                                                                          let Rd :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              5)
                                                                                                          let Rn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              5)
                                                                                                          let imm4 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              11
                                                                                                              4)
                                                                                                          let imm5 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              5)
                                                                                                          (decode_ins_advsimd_elt_aarch64_instrs_vector_transfer_vector_insert
                                                                                                            Rd
                                                                                                            Rn
                                                                                                            imm4
                                                                                                            imm5)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__677 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     21)) == (0b01001110000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     15
                                                                                                                     10)) == (0b000111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__676 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__676 <b 481) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__677 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 481
                                                                                                              let Rd :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  5)
                                                                                                              let Rn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  5)
                                                                                                              let imm5 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  5)
                                                                                                              (decode_ins_advsimd_gen_aarch64_instrs_vector_transfer_integer_insert
                                                                                                                Rd
                                                                                                                Rn
                                                                                                                imm5)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__679 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           29
                                                                                                                           24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             21
                                                                                                                             21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             15
                                                                                                                             10)) == (0b100101#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__678 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__678 <b 692) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__679 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 692
                                                                                                                  let Rd :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      5)
                                                                                                                  let Rn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      5
                                                                                                                      5)
                                                                                                                  let Rm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      5)
                                                                                                                  let size :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      2)
                                                                                                                  let U :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      29
                                                                                                                      1)
                                                                                                                  let Q :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      30
                                                                                                                      1)
                                                                                                                  (decode_mla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum
                                                                                                                    Rd
                                                                                                                    Rn
                                                                                                                    Rm
                                                                                                                    size
                                                                                                                    U
                                                                                                                    Q)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__681 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               29
                                                                                                                               24)) == (0b101110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 21
                                                                                                                                 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 15
                                                                                                                                 10)) == (0b100101#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__680 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__680 <b 693) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__681 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 693
                                                                                                                      let Rd :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          5)
                                                                                                                      let Rn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          5
                                                                                                                          5)
                                                                                                                      let Rm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          5)
                                                                                                                      let size :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          2)
                                                                                                                      let U :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          29
                                                                                                                          1)
                                                                                                                      let Q :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          30
                                                                                                                          1)
                                                                                                                      (decode_mls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum
                                                                                                                        Rd
                                                                                                                        Rn
                                                                                                                        Rm
                                                                                                                        size
                                                                                                                        U
                                                                                                                        Q)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__683 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   29
                                                                                                                                   24)) == (0b101111#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     15
                                                                                                                                     12)) == (0x0#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     10
                                                                                                                                     10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__682 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__682 <b 694) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__683 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 694
                                                                                                                          let Rd :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              5)
                                                                                                                          let Rn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              5
                                                                                                                              5)
                                                                                                                          let H :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              11
                                                                                                                              1)
                                                                                                                          let o2 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              14
                                                                                                                              1)
                                                                                                                          let Rm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              4)
                                                                                                                          let M :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              20
                                                                                                                              1)
                                                                                                                          let L :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              21
                                                                                                                              1)
                                                                                                                          let size :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              2)
                                                                                                                          let Q :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              30
                                                                                                                              1)
                                                                                                                          (decode_mla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int
                                                                                                                            Rd
                                                                                                                            Rn
                                                                                                                            H
                                                                                                                            o2
                                                                                                                            Rm
                                                                                                                            M
                                                                                                                            L
                                                                                                                            size
                                                                                                                            Q)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__685 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       29
                                                                                                                                       24)) == (0b101111#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         15
                                                                                                                                         12)) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         10
                                                                                                                                         10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__684 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__684 <b 695) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__685 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 695
                                                                                                                              let Rd :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  5)
                                                                                                                              let Rn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  5
                                                                                                                                  5)
                                                                                                                              let H :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  11
                                                                                                                                  1)
                                                                                                                              let o2 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  14
                                                                                                                                  1)
                                                                                                                              let Rm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  4)
                                                                                                                              let M :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  20
                                                                                                                                  1)
                                                                                                                              let L :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  21
                                                                                                                                  1)
                                                                                                                              let size :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  2)
                                                                                                                              let Q :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  30
                                                                                                                                  1)
                                                                                                                              (decode_mls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int
                                                                                                                                Rd
                                                                                                                                Rn
                                                                                                                                H
                                                                                                                                o2
                                                                                                                                Rm
                                                                                                                                M
                                                                                                                                L
                                                                                                                                size
                                                                                                                                Q)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__687 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           29
                                                                                                                                           24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             21
                                                                                                                                             21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             15
                                                                                                                                             10)) == (0b100111#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__686 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__686 <b 704) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__687 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 704
                                                                                                                                  let Rd :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      5)
                                                                                                                                  let Rn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      5
                                                                                                                                      5)
                                                                                                                                  let Rm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      5)
                                                                                                                                  let size :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      2)
                                                                                                                                  let U :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      29
                                                                                                                                      1)
                                                                                                                                  let Q :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      30
                                                                                                                                      1)
                                                                                                                                  (decode_mul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product
                                                                                                                                    Rd
                                                                                                                                    Rn
                                                                                                                                    Rm
                                                                                                                                    size
                                                                                                                                    U
                                                                                                                                    Q)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__689 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               29
                                                                                                                                               24)) == (0b101110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 21
                                                                                                                                                 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 15
                                                                                                                                                 10)) == (0b100111#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__688 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__688 <b 705) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__689 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 705
                                                                                                                                      let Rd :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          5)
                                                                                                                                      let Rn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          5
                                                                                                                                          5)
                                                                                                                                      let Rm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          5)
                                                                                                                                      let size :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          2)
                                                                                                                                      let U :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          29
                                                                                                                                          1)
                                                                                                                                      let Q :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          30
                                                                                                                                          1)
                                                                                                                                      (decode_pmul_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product
                                                                                                                                        Rd
                                                                                                                                        Rn
                                                                                                                                        Rm
                                                                                                                                        size
                                                                                                                                        U
                                                                                                                                        Q)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__691 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   29
                                                                                                                                                   24)) == (0b001111#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     15
                                                                                                                                                     12)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     10
                                                                                                                                                     10)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__690 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__690 <b 706) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__691 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 706
                                                                                                                                          let Rd :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              5)
                                                                                                                                          let Rn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              5)
                                                                                                                                          let H :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              11
                                                                                                                                              1)
                                                                                                                                          let Rm :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              4)
                                                                                                                                          let M :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              20
                                                                                                                                              1)
                                                                                                                                          let L :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              21
                                                                                                                                              1)
                                                                                                                                          let size :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              22
                                                                                                                                              2)
                                                                                                                                          let Q :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              30
                                                                                                                                              1)
                                                                                                                                          (decode_mul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_int
                                                                                                                                            Rd
                                                                                                                                            Rn
                                                                                                                                            H
                                                                                                                                            Rm
                                                                                                                                            M
                                                                                                                                            L
                                                                                                                                            size
                                                                                                                                            Q)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__693 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     29
                                                                                                                                                     10)) == (0xB8816#20 : (BitVec 20)))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__692 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__692 <b 707) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__693 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 707
                                                                                                                                              let Rd :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  5)
                                                                                                                                              let Rn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  5
                                                                                                                                                  5)
                                                                                                                                              let Q :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  30
                                                                                                                                                  1)
                                                                                                                                              (decode_not_advsimd_aarch64_instrs_vector_arithmetic_unary_not
                                                                                                                                                Rd
                                                                                                                                                Rn
                                                                                                                                                Q)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__695 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           29
                                                                                                                                                           24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             21
                                                                                                                                                             21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             15
                                                                                                                                                             10)) == (0b111000#6 : (BitVec 6)))))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__694 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__694 <b 715) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__695 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 715
                                                                                                                                                  let Rd :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      5)
                                                                                                                                                  let Rn :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      5
                                                                                                                                                      5)
                                                                                                                                                  let Rm :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      16
                                                                                                                                                      5)
                                                                                                                                                  let size :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      22
                                                                                                                                                      2)
                                                                                                                                                  let Q :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      30
                                                                                                                                                      1)
                                                                                                                                                  (decode_pmull_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly
                                                                                                                                                    Rd
                                                                                                                                                    Rn
                                                                                                                                                    Rm
                                                                                                                                                    size
                                                                                                                                                    Q)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__697 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             21)) == (0b11001110011#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             15
                                                                                                                                                             10)) == (0b100011#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__696 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__696 <b 717) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__697 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 717
                                                                                                                                                      let Rd :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          5)
                                                                                                                                                      let Rn :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          5
                                                                                                                                                          5)
                                                                                                                                                      let Rm :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          16
                                                                                                                                                          5)
                                                                                                                                                      (decode_rax1_advsimd_aarch64_instrs_vector_crypto_sha3_rax1
                                                                                                                                                        Rd
                                                                                                                                                        Rn
                                                                                                                                                        Rm)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__699 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 29
                                                                                                                                                                 10)) == (0xB9816#20 : (BitVec 20)))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__698 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__698 <b 718) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__699 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 718
                                                                                                                                                          let Rd :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              0
                                                                                                                                                              5)
                                                                                                                                                          let Rn :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              5
                                                                                                                                                              5)
                                                                                                                                                          let Q :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              30
                                                                                                                                                              1)
                                                                                                                                                          (decode_rbit_advsimd_aarch64_instrs_vector_arithmetic_unary_rbit
                                                                                                                                                            Rd
                                                                                                                                                            Rn
                                                                                                                                                            Q)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__701 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     31
                                                                                                                                                                     31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       29
                                                                                                                                                                       24)) == (0b001110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       21
                                                                                                                                                                       10)) == (0x806#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__700 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__700 <b 739) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__701 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 739
                                                                                                                                                              let Rd :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  0
                                                                                                                                                                  5)
                                                                                                                                                              let Rn :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  5
                                                                                                                                                                  5)
                                                                                                                                                              let o0 :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  12
                                                                                                                                                                  1)
                                                                                                                                                              let size :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  22
                                                                                                                                                                  2)
                                                                                                                                                              let U :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  29
                                                                                                                                                                  1)
                                                                                                                                                              let Q :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  30
                                                                                                                                                                  1)
                                                                                                                                                              (decode_rev16_advsimd_aarch64_instrs_vector_arithmetic_unary_rev
                                                                                                                                                                Rd
                                                                                                                                                                Rn
                                                                                                                                                                o0
                                                                                                                                                                size
                                                                                                                                                                U
                                                                                                                                                                Q)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__703 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         31
                                                                                                                                                                         31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           29
                                                                                                                                                                           24)) == (0b101110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           21
                                                                                                                                                                           10)) == (0x802#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__702 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__702 <b 740) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__703 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 740
                                                                                                                                                                  let Rd :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      0
                                                                                                                                                                      5)
                                                                                                                                                                  let Rn :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      5
                                                                                                                                                                      5)
                                                                                                                                                                  let o0 :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      12
                                                                                                                                                                      1)
                                                                                                                                                                  let size :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      22
                                                                                                                                                                      2)
                                                                                                                                                                  let U :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      29
                                                                                                                                                                      1)
                                                                                                                                                                  let Q :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      30
                                                                                                                                                                      1)
                                                                                                                                                                  (decode_rev32_advsimd_aarch64_instrs_vector_arithmetic_unary_rev
                                                                                                                                                                    Rd
                                                                                                                                                                    Rn
                                                                                                                                                                    o0
                                                                                                                                                                    size
                                                                                                                                                                    U
                                                                                                                                                                    Q)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__705 ← (( do
                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             31
                                                                                                                                                                             31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                               __opcode
                                                                                                                                                                               29
                                                                                                                                                                               24)) == (0b001110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                               __opcode
                                                                                                                                                                               21
                                                                                                                                                                               10)) == (0x802#12 : (BitVec 12))))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__704 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__704 <b 741) : Bool))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false)
                                                                                                                                                                    )
                                                                                                                                                                    :
                                                                                                                                                                    SailM
                                                                                                                                                                    Bool
                                                                                                                                                                    )
                                                                                                                                                                  if (w__705 : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 741
                                                                                                                                                                      let Rd :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          0
                                                                                                                                                                          5)
                                                                                                                                                                      let Rn :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          5
                                                                                                                                                                          5)
                                                                                                                                                                      let o0 :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          12
                                                                                                                                                                          1)
                                                                                                                                                                      let size :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          22
                                                                                                                                                                          2)
                                                                                                                                                                      let U :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          29
                                                                                                                                                                          1)
                                                                                                                                                                      let Q :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          30
                                                                                                                                                                          1)
                                                                                                                                                                      (decode_rev64_advsimd_aarch64_instrs_vector_arithmetic_unary_rev
                                                                                                                                                                        Rd
                                                                                                                                                                        Rn
                                                                                                                                                                        o0
                                                                                                                                                                        size
                                                                                                                                                                        U
                                                                                                                                                                        Q)
                                                                                                                                                                      (pure false))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      let w__707 ← (( do
                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 31
                                                                                                                                                                                 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                                                   __opcode
                                                                                                                                                                                   29
                                                                                                                                                                                   23)) == (0b0011110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                   __opcode
                                                                                                                                                                                   15
                                                                                                                                                                                   10)) == (0b100011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            let w__706 ← (( do
                                                                                                                                                                              readReg SEE
                                                                                                                                                                              )
                                                                                                                                                                              :
                                                                                                                                                                              SailM
                                                                                                                                                                              Int
                                                                                                                                                                              )
                                                                                                                                                                            (pure (((w__706 <b 744) : Bool))))
                                                                                                                                                                        else
                                                                                                                                                                          (pure false)
                                                                                                                                                                        )
                                                                                                                                                                        :
                                                                                                                                                                        SailM
                                                                                                                                                                        Bool
                                                                                                                                                                        )
                                                                                                                                                                      if (w__707 : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 744
                                                                                                                                                                          let Rd :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              0
                                                                                                                                                                              5)
                                                                                                                                                                          let Rn :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              5
                                                                                                                                                                              5)
                                                                                                                                                                          let op :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              11
                                                                                                                                                                              1)
                                                                                                                                                                          let immb :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              16
                                                                                                                                                                              3)
                                                                                                                                                                          let immh :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              19
                                                                                                                                                                              4)
                                                                                                                                                                          let Q :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              30
                                                                                                                                                                              1)
                                                                                                                                                                          (decode_rshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical
                                                                                                                                                                            Rd
                                                                                                                                                                            Rn
                                                                                                                                                                            op
                                                                                                                                                                            immb
                                                                                                                                                                            immh
                                                                                                                                                                            Q)
                                                                                                                                                                          (pure false))
                                                                                                                                                                      else
                                                                                                                                                                        (pure true))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
