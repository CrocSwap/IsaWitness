import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0917
import ArmFull.Fn.M0997
import ArmFull.Fn.M0998

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
def __DecodeA64_SME__seg12 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__847 ← (( do
    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11000001111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               __opcode 16 15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                 __opcode 12 10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                 __opcode 5 2)) == (0x6#4 : (BitVec 4)))))) : Bool) : Bool)
    then
      (do
        let w__846 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__846 <b 2617) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__847 : Bool)
  then
    (do
      writeReg SEE 2617
      let Zm := (BitVec.slice __opcode 17 4)
      let Rv := (BitVec.slice __opcode 13 2)
      let Zn := (BitVec.slice __opcode 6 4)
      let U := (BitVec.slice __opcode 4 1)
      let S := (BitVec.slice __opcode 3 1)
      let off2 := (BitVec.slice __opcode 0 2)
      (decode_UMLSL_ZA_ZZW_2x2 Zm Rv Zn U S off2)
      (pure false))
  else
    (do
      let w__849 ← (( do
        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11000001111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                   __opcode 16 15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                     __opcode 12 10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                     __opcode 5 2)) == (0x0#4 : (BitVec 4)))))) : Bool) : Bool)
        then
          (do
            let w__848 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__848 <b 2618) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__849 : Bool)
      then
        (do
          writeReg SEE 2618
          let Zm := (BitVec.slice __opcode 17 4)
          let Rv := (BitVec.slice __opcode 13 2)
          let Zn := (BitVec.slice __opcode 6 4)
          let U := (BitVec.slice __opcode 4 1)
          let S := (BitVec.slice __opcode 3 1)
          let off2 := (BitVec.slice __opcode 0 2)
          (decode_SMLAL_ZA_ZZW_2x2 Zm Rv Zn U S off2)
          (pure false))
      else
        (do
          let w__851 ← (( do
            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11000001111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                       __opcode 16 15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                         __opcode 12 10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                         __opcode 5 2)) == (0x2#4 : (BitVec 4)))))) : Bool) : Bool)
            then
              (do
                let w__850 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__850 <b 2619) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__851 : Bool)
          then
            (do
              writeReg SEE 2619
              let Zm := (BitVec.slice __opcode 17 4)
              let Rv := (BitVec.slice __opcode 13 2)
              let Zn := (BitVec.slice __opcode 6 4)
              let U := (BitVec.slice __opcode 4 1)
              let S := (BitVec.slice __opcode 3 1)
              let off2 := (BitVec.slice __opcode 0 2)
              (decode_SMLSL_ZA_ZZW_2x2 Zm Rv Zn U S off2)
              (pure false))
          else
            (do
              let w__853 ← (( do
                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xC16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                             __opcode 12 10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                             __opcode 4 2)) == (0b100#3 : (BitVec 3)))))) : Bool) : Bool)
                then
                  (do
                    let w__852 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__852 <b 2620) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__853 : Bool)
              then
                (do
                  writeReg SEE 2620
                  let Zm := (BitVec.slice __opcode 16 4)
                  let Rv := (BitVec.slice __opcode 13 2)
                  let Zn := (BitVec.slice __opcode 5 5)
                  let U := (BitVec.slice __opcode 4 1)
                  let S := (BitVec.slice __opcode 3 1)
                  let off2 := (BitVec.slice __opcode 0 2)
                  (decode_UMLAL_ZA_ZZV_2x1 Zm Rv Zn U S off2)
                  (pure false))
              else
                (do
                  let w__855 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xC16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                 __opcode 12 10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                 __opcode 4 2)) == (0b110#3 : (BitVec 3)))))) : Bool) : Bool)
                    then
                      (do
                        let w__854 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__854 <b 2621) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__855 : Bool)
                  then
                    (do
                      writeReg SEE 2621
                      let Zm := (BitVec.slice __opcode 16 4)
                      let Rv := (BitVec.slice __opcode 13 2)
                      let Zn := (BitVec.slice __opcode 5 5)
                      let U := (BitVec.slice __opcode 4 1)
                      let S := (BitVec.slice __opcode 3 1)
                      let off2 := (BitVec.slice __opcode 0 2)
                      (decode_UMLSL_ZA_ZZV_2x1 Zm Rv Zn U S off2)
                      (pure false))
                  else
                    (do
                      let w__857 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31
                                 20)) == (0xC16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                     __opcode 12 10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                     __opcode 4 2)) == (0b000#3 : (BitVec 3)))))) : Bool) : Bool)
                        then
                          (do
                            let w__856 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__856 <b 2622) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__857 : Bool)
                      then
                        (do
                          writeReg SEE 2622
                          let Zm := (BitVec.slice __opcode 16 4)
                          let Rv := (BitVec.slice __opcode 13 2)
                          let Zn := (BitVec.slice __opcode 5 5)
                          let U := (BitVec.slice __opcode 4 1)
                          let S := (BitVec.slice __opcode 3 1)
                          let off2 := (BitVec.slice __opcode 0 2)
                          (decode_SMLAL_ZA_ZZV_2x1 Zm Rv Zn U S off2)
                          (pure false))
                      else
                        (do
                          let w__859 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode
                                     31 20)) == (0xC16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                         __opcode 12 10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                         __opcode 4 2)) == (0b010#3 : (BitVec 3)))))) : Bool) : Bool)
                            then
                              (do
                                let w__858 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__858 <b 2623) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__859 : Bool)
                          then
                            (do
                              writeReg SEE 2623
                              let Zm := (BitVec.slice __opcode 16 4)
                              let Rv := (BitVec.slice __opcode 13 2)
                              let Zn := (BitVec.slice __opcode 5 5)
                              let U := (BitVec.slice __opcode 4 1)
                              let S := (BitVec.slice __opcode 3 1)
                              let off2 := (BitVec.slice __opcode 0 2)
                              (decode_SMLSL_ZA_ZZV_2x1 Zm Rv Zn U S off2)
                              (pure false))
                          else
                            (do
                              let w__861 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                         __opcode 31 21)) == (0b11000001111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                           __opcode 17 15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                             __opcode 12 10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                             __opcode 6 2)) == (0b00100#5 : (BitVec 5)))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__860 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__860 <b 2624) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__861 : Bool)
                              then
                                (do
                                  writeReg SEE 2624
                                  let Zm := (BitVec.slice __opcode 18 3)
                                  let Rv := (BitVec.slice __opcode 13 2)
                                  let Zn := (BitVec.slice __opcode 7 3)
                                  let U := (BitVec.slice __opcode 4 1)
                                  let S := (BitVec.slice __opcode 3 1)
                                  let off2 := (BitVec.slice __opcode 0 2)
                                  (decode_UMLAL_ZA_ZZW_4x4 Zm Rv Zn U S off2)
                                  (pure false))
                              else
                                (do
                                  let w__863 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                             __opcode 31 21)) == (0b11000001111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                               __opcode 17 15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                 __opcode 12 10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                 __opcode 6 2)) == (0b00110#5 : (BitVec 5)))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__862 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__862 <b 2625) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__863 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2625
                                      let Zm := (BitVec.slice __opcode 18 3)
                                      let Rv := (BitVec.slice __opcode 13 2)
                                      let Zn := (BitVec.slice __opcode 7 3)
                                      let U := (BitVec.slice __opcode 4 1)
                                      let S := (BitVec.slice __opcode 3 1)
                                      let off2 := (BitVec.slice __opcode 0 2)
                                      (decode_UMLSL_ZA_ZZW_4x4 Zm Rv Zn U S off2)
                                      (pure false))
                                  else
                                    (do
                                      let w__865 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                 __opcode 31 21)) == (0b11000001111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                   __opcode 17 15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                     __opcode 12 10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                     __opcode 6 2)) == (0b00000#5 : (BitVec 5)))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__864 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__864 <b 2626) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__865 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2626
                                          let Zm := (BitVec.slice __opcode 18 3)
                                          let Rv := (BitVec.slice __opcode 13 2)
                                          let Zn := (BitVec.slice __opcode 7 3)
                                          let U := (BitVec.slice __opcode 4 1)
                                          let S := (BitVec.slice __opcode 3 1)
                                          let off2 := (BitVec.slice __opcode 0 2)
                                          (decode_SMLAL_ZA_ZZW_4x4 Zm Rv Zn U S off2)
                                          (pure false))
                                      else
                                        (do
                                          let w__867 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                     __opcode 31 21)) == (0b11000001111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                       __opcode 17 15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                         __opcode 12 10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                         __opcode 6 2)) == (0b00010#5 : (BitVec 5)))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__866 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__866 <b 2627) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__867 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2627
                                              let Zm := (BitVec.slice __opcode 18 3)
                                              let Rv := (BitVec.slice __opcode 13 2)
                                              let Zn := (BitVec.slice __opcode 7 3)
                                              let U := (BitVec.slice __opcode 4 1)
                                              let S := (BitVec.slice __opcode 3 1)
                                              let off2 := (BitVec.slice __opcode 0 2)
                                              (decode_SMLSL_ZA_ZZW_4x4 Zm Rv Zn U S off2)
                                              (pure false))
                                          else
                                            (do
                                              let w__869 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                         __opcode 31 20)) == (0xC17#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                             __opcode 12 10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                             __opcode 4 2)) == (0b100#3 : (BitVec 3)))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__868 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__868 <b 2628) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__869 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2628
                                                  let Zm := (BitVec.slice __opcode 16 4)
                                                  let Rv := (BitVec.slice __opcode 13 2)
                                                  let Zn := (BitVec.slice __opcode 5 5)
                                                  let U := (BitVec.slice __opcode 4 1)
                                                  let S := (BitVec.slice __opcode 3 1)
                                                  let off2 := (BitVec.slice __opcode 0 2)
                                                  (decode_UMLAL_ZA_ZZV_4x1 Zm Rv Zn U S off2)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__871 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                             __opcode 31 20)) == (0xC17#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                 __opcode 12 10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                 __opcode 4 2)) == (0b110#3 : (BitVec 3)))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__870 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__870 <b 2629) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__871 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2629
                                                      let Zm := (BitVec.slice __opcode 16 4)
                                                      let Rv := (BitVec.slice __opcode 13 2)
                                                      let Zn := (BitVec.slice __opcode 5 5)
                                                      let U := (BitVec.slice __opcode 4 1)
                                                      let S := (BitVec.slice __opcode 3 1)
                                                      let off2 := (BitVec.slice __opcode 0 2)
                                                      (decode_UMLSL_ZA_ZZV_4x1 Zm Rv Zn U S off2)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__873 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                 __opcode 31 20)) == (0xC17#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                     __opcode 12 10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                     __opcode 4 2)) == (0b000#3 : (BitVec 3)))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__872 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__872 <b 2630) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__873 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2630
                                                          let Zm := (BitVec.slice __opcode 16 4)
                                                          let Rv := (BitVec.slice __opcode 13 2)
                                                          let Zn := (BitVec.slice __opcode 5 5)
                                                          let U := (BitVec.slice __opcode 4 1)
                                                          let S := (BitVec.slice __opcode 3 1)
                                                          let off2 := (BitVec.slice __opcode 0 2)
                                                          (decode_SMLAL_ZA_ZZV_4x1 Zm Rv Zn U S off2)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__875 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                     __opcode 31 20)) == (0xC17#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                         __opcode 12 10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                         __opcode 4 2)) == (0b010#3 : (BitVec 3)))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__874 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__874 <b 2631) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__875 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2631
                                                              let Zm := (BitVec.slice __opcode 16 4)
                                                              let Rv := (BitVec.slice __opcode 13 2)
                                                              let Zn := (BitVec.slice __opcode 5 5)
                                                              let U := (BitVec.slice __opcode 4 1)
                                                              let S := (BitVec.slice __opcode 3 1)
                                                              let off2 :=
                                                                (BitVec.slice __opcode 0 2)
                                                              (decode_SMLSL_ZA_ZZV_4x1 Zm Rv Zn U S
                                                                off2)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__877 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                         __opcode 31 20)) == (0xC1C#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                           __opcode 4 3)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__876 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__876 <b 2632) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__877 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2632
                                                                  let Zm :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let i3h :=
                                                                    (BitVec.slice __opcode 15 1)
                                                                  let Rv :=
                                                                    (BitVec.slice __opcode 13 2)
                                                                  let i3l :=
                                                                    (BitVec.slice __opcode 10 2)
                                                                  let Zn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let U :=
                                                                    (BitVec.slice __opcode 4 1)
                                                                  let S :=
                                                                    (BitVec.slice __opcode 3 1)
                                                                  let off3 :=
                                                                    (BitVec.slice __opcode 0 3)
                                                                  (decode_UMLAL_ZA_ZZi_1 Zm i3h Rv
                                                                    i3l Zn U S off3)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__879 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                             __opcode 31 20)) == (0xC1C#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                               __opcode 4 3)) == (0b11#2 : (BitVec 2))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__878 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__878 <b 2633) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__879 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2633
                                                                      let Zm :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let i3h :=
                                                                        (BitVec.slice __opcode 15 1)
                                                                      let Rv :=
                                                                        (BitVec.slice __opcode 13 2)
                                                                      let i3l :=
                                                                        (BitVec.slice __opcode 10 2)
                                                                      let Zn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let U :=
                                                                        (BitVec.slice __opcode 4 1)
                                                                      let S :=
                                                                        (BitVec.slice __opcode 3 1)
                                                                      let off3 :=
                                                                        (BitVec.slice __opcode 0 3)
                                                                      (decode_UMLSL_ZA_ZZi_1 Zm i3h
                                                                        Rv i3l Zn U S off3)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__881 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 20)) == (0xC1C#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                   __opcode 4 3)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__880 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__880 <b 2634) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__881 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2634
                                                                          let Zm :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let i3h :=
                                                                            (BitVec.slice __opcode
                                                                              15 1)
                                                                          let Rv :=
                                                                            (BitVec.slice __opcode
                                                                              13 2)
                                                                          let i3l :=
                                                                            (BitVec.slice __opcode
                                                                              10 2)
                                                                          let Zn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let U :=
                                                                            (BitVec.slice __opcode 4
                                                                              1)
                                                                          let S :=
                                                                            (BitVec.slice __opcode 3
                                                                              1)
                                                                          let off3 :=
                                                                            (BitVec.slice __opcode 0
                                                                              3)
                                                                          (decode_SMLAL_ZA_ZZi_1 Zm
                                                                            i3h Rv i3l Zn U S off3)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__883 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 20)) == (0xC1C#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 12
                                                                                       12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                       __opcode 4 3)) == (0b01#2 : (BitVec 2))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__882 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__882 <b 2635) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__883 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2635
                                                                              let Zm :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let i3h :=
                                                                                (BitVec.slice
                                                                                  __opcode 15 1)
                                                                              let Rv :=
                                                                                (BitVec.slice
                                                                                  __opcode 13 2)
                                                                              let i3l :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 2)
                                                                              let Zn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let U :=
                                                                                (BitVec.slice
                                                                                  __opcode 4 1)
                                                                              let S :=
                                                                                (BitVec.slice
                                                                                  __opcode 3 1)
                                                                              let off3 :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 3)
                                                                              (decode_SMLSL_ZA_ZZi_1
                                                                                Zm i3h Rv i3l Zn U S
                                                                                off3)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__885 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         20)) == (0xC1D#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             5 3)) == (0b010#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__884 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__884 <b 2636) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__885 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2636
                                                                                  let Zm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Rv :=
                                                                                    (BitVec.slice
                                                                                      __opcode 13 2)
                                                                                  let i3h :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 2)
                                                                                  let Zn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 6 4)
                                                                                  let U :=
                                                                                    (BitVec.slice
                                                                                      __opcode 4 1)
                                                                                  let S :=
                                                                                    (BitVec.slice
                                                                                      __opcode 3 1)
                                                                                  let i3l :=
                                                                                    (BitVec.slice
                                                                                      __opcode 2 1)
                                                                                  let off2 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 2)
                                                                                  (decode_UMLAL_ZA_ZZi_2xi
                                                                                    Zm Rv i3h Zn U S
                                                                                    i3l off2)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__887 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 20)) == (0xC1D#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 12
                                                                                                 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 5 3)) == (0b011#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__886 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__886 <b 2637) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__887 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2637
                                                                                      let Zm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let Rv :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          13 2)
                                                                                      let i3h :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 2)
                                                                                      let Zn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 6
                                                                                          4)
                                                                                      let U :=
                                                                                        (BitVec.slice
                                                                                          __opcode 4
                                                                                          1)
                                                                                      let S :=
                                                                                        (BitVec.slice
                                                                                          __opcode 3
                                                                                          1)
                                                                                      let i3l :=
                                                                                        (BitVec.slice
                                                                                          __opcode 2
                                                                                          1)
                                                                                      let off2 :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          2)
                                                                                      (decode_UMLSL_ZA_ZZi_2xi
                                                                                        Zm Rv i3h Zn
                                                                                        U S i3l off2)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__889 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 20)) == (0xC1D#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   15
                                                                                                   15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     12
                                                                                                     12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     5
                                                                                                     3)) == (0b000#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__888 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__888 <b 2638) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__889 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2638
                                                                                          let Zm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Rv :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              13 2)
                                                                                          let i3h :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 2)
                                                                                          let Zn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              6 4)
                                                                                          let U :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              4 1)
                                                                                          let S :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              3 1)
                                                                                          let i3l :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              2 1)
                                                                                          let off2 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 2)
                                                                                          (decode_SMLAL_ZA_ZZi_2xi
                                                                                            Zm Rv
                                                                                            i3h Zn U
                                                                                            S i3l
                                                                                            off2)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__891 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     20)) == (0xC1D#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       15
                                                                                                       15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         12
                                                                                                         12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         5
                                                                                                         3)) == (0b001#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__890 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__890 <b 2639) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__891 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2639
                                                                                              let Zm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  4)
                                                                                              let Rv :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  13
                                                                                                  2)
                                                                                              let i3h :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  10
                                                                                                  2)
                                                                                              let Zn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  6
                                                                                                  4)
                                                                                              let U :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  4
                                                                                                  1)
                                                                                              let S :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  3
                                                                                                  1)
                                                                                              let i3l :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  2
                                                                                                  1)
                                                                                              let off2 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  2)
                                                                                              (decode_SMLSL_ZA_ZZi_2xi
                                                                                                Zm
                                                                                                Rv
                                                                                                i3h
                                                                                                Zn U
                                                                                                S
                                                                                                i3l
                                                                                                off2)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__893 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         20)) == (0xC1D#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           15
                                                                                                           15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             12
                                                                                                             12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             6
                                                                                                             3)) == (0x2#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__892 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__892 <b 2640) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__893 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2640
                                                                                                  let Zm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      4)
                                                                                                  let Rv :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      13
                                                                                                      2)
                                                                                                  let i3h :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      10
                                                                                                      2)
                                                                                                  let Zn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      7
                                                                                                      3)
                                                                                                  let U :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      4
                                                                                                      1)
                                                                                                  let S :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      3
                                                                                                      1)
                                                                                                  let i3l :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      2
                                                                                                      1)
                                                                                                  let off2 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      2)
                                                                                                  (decode_UMLAL_ZA_ZZi_4xi
                                                                                                    Zm
                                                                                                    Rv
                                                                                                    i3h
                                                                                                    Zn
                                                                                                    U
                                                                                                    S
                                                                                                    i3l
                                                                                                    off2)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__895 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             20)) == (0xC1D#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 12
                                                                                                                 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 6
                                                                                                                 3)) == (0x3#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__894 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__894 <b 2641) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__895 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 2641
                                                                                                      let Zm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          4)
                                                                                                      let Rv :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          13
                                                                                                          2)
                                                                                                      let i3h :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          10
                                                                                                          2)
                                                                                                      let Zn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          7
                                                                                                          3)
                                                                                                      let U :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          4
                                                                                                          1)
                                                                                                      let S :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          3
                                                                                                          1)
                                                                                                      let i3l :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          2
                                                                                                          1)
                                                                                                      let off2 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          2)
                                                                                                      (decode_UMLSL_ZA_ZZi_4xi
                                                                                                        Zm
                                                                                                        Rv
                                                                                                        i3h
                                                                                                        Zn
                                                                                                        U
                                                                                                        S
                                                                                                        i3l
                                                                                                        off2)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__897 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 20)) == (0xC1D#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   15
                                                                                                                   15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     12
                                                                                                                     12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     6
                                                                                                                     3)) == (0x0#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__896 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__896 <b 2642) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__897 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 2642
                                                                                                          let Zm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              4)
                                                                                                          let Rv :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              13
                                                                                                              2)
                                                                                                          let i3h :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              10
                                                                                                              2)
                                                                                                          let Zn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              7
                                                                                                              3)
                                                                                                          let U :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              4
                                                                                                              1)
                                                                                                          let S :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              3
                                                                                                              1)
                                                                                                          let i3l :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              2
                                                                                                              1)
                                                                                                          let off2 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              2)
                                                                                                          (decode_SMLAL_ZA_ZZi_4xi
                                                                                                            Zm
                                                                                                            Rv
                                                                                                            i3h
                                                                                                            Zn
                                                                                                            U
                                                                                                            S
                                                                                                            i3l
                                                                                                            off2)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__899 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     20)) == (0xC1D#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       15
                                                                                                                       15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         12
                                                                                                                         12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         6
                                                                                                                         3)) == (0x1#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__898 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__898 <b 2643) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__899 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 2643
                                                                                                              let Zm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  4)
                                                                                                              let Rv :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  13
                                                                                                                  2)
                                                                                                              let i3h :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  10
                                                                                                                  2)
                                                                                                              let Zn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  7
                                                                                                                  3)
                                                                                                              let U :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  4
                                                                                                                  1)
                                                                                                              let S :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  3
                                                                                                                  1)
                                                                                                              let i3l :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  2
                                                                                                                  1)
                                                                                                              let off2 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  2)
                                                                                                              (decode_SMLSL_ZA_ZZi_4xi
                                                                                                                Zm
                                                                                                                Rv
                                                                                                                i3h
                                                                                                                Zn
                                                                                                                U
                                                                                                                S
                                                                                                                i3l
                                                                                                                off2)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__901 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           21
                                                                                                                           21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             16
                                                                                                                             5)) == (0x580#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             0
                                                                                                                             0)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__900 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__900 <b 2644) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__901 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 2644
                                                                                                                  let size :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      2)
                                                                                                                  let Zm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      17
                                                                                                                      4)
                                                                                                                  let Zdn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      1
                                                                                                                      4)
                                                                                                                  let U :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      1)
                                                                                                                  (decode_UMAX_MZ_ZZW_2x2
                                                                                                                    size
                                                                                                                    Zm
                                                                                                                    Zdn
                                                                                                                    U)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__903 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               21
                                                                                                                               21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 16
                                                                                                                                 5)) == (0x580#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 0
                                                                                                                                 0)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__902 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__902 <b 2645) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__903 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 2645
                                                                                                                      let size :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          2)
                                                                                                                      let Zm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          17
                                                                                                                          4)
                                                                                                                      let Zdn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          1
                                                                                                                          4)
                                                                                                                      let U :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          1)
                                                                                                                      (decode_SMAX_MZ_ZZW_2x2
                                                                                                                        size
                                                                                                                        Zm
                                                                                                                        Zdn
                                                                                                                        U)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__905 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   21
                                                                                                                                   20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     15
                                                                                                                                     5)) == (0b10100000000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     0
                                                                                                                                     0)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__904 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__904 <b 2646) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__905 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 2646
                                                                                                                          let size :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              2)
                                                                                                                          let Zm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              4)
                                                                                                                          let Zdn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              1
                                                                                                                              4)
                                                                                                                          let U :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              1)
                                                                                                                          (decode_UMAX_MZ_ZZV_2x1
                                                                                                                            size
                                                                                                                            Zm
                                                                                                                            Zdn
                                                                                                                            U)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__907 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       21
                                                                                                                                       20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         15
                                                                                                                                         5)) == (0b10100000000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         0
                                                                                                                                         0)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__906 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__906 <b 2647) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__907 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 2647
                                                                                                                              let size :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  2)
                                                                                                                              let Zm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  4)
                                                                                                                              let Zdn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  1
                                                                                                                                  4)
                                                                                                                              let U :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  1)
                                                                                                                              (decode_SMAX_MZ_ZZV_2x1
                                                                                                                                size
                                                                                                                                Zm
                                                                                                                                Zdn
                                                                                                                                U)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__909 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           21
                                                                                                                                           21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             17
                                                                                                                                             5)) == (0b0010111000000#13 : (BitVec 13))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             1
                                                                                                                                             0)) == (0b01#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__908 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__908 <b 2648) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__909 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 2648
                                                                                                                                  let size :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      2)
                                                                                                                                  let Zm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      18
                                                                                                                                      3)
                                                                                                                                  let Zdn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      2
                                                                                                                                      3)
                                                                                                                                  let U :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      1)
                                                                                                                                  (decode_UMAX_MZ_ZZW_4x4
                                                                                                                                    size
                                                                                                                                    Zm
                                                                                                                                    Zdn
                                                                                                                                    U)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__911 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             24)) == (0xC1#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               21
                                                                                                                                               21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 17
                                                                                                                                                 5)) == (0b0010111000000#13 : (BitVec 13))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 1
                                                                                                                                                 0)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__910 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__910 <b 2649) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__911 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 2649
                                                                                                                                      let size :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          2)
                                                                                                                                      let Zm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          18
                                                                                                                                          3)
                                                                                                                                      let Zdn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          2
                                                                                                                                          3)
                                                                                                                                      let U :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          1)
                                                                                                                                      (decode_SMAX_MZ_ZZW_4x4
                                                                                                                                        size
                                                                                                                                        Zm
                                                                                                                                        Zdn
                                                                                                                                        U)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (pure true)))))))))))))))))))))))))))))))))


end ArmFull.Functions
