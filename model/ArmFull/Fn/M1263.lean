import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0922
import ArmFull.Fn.M0999
import ArmFull.Fn.M1000
import ArmFull.Fn.M1168
import ArmFull.Fn.M1169

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
def __DecodeA64_SME__seg15 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__1087 ← (( do
    if (((((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb __opcode 31 18)) == (0b11000000100111#14 : (BitVec 14))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               __opcode 15 14)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                 __opcode 11 10)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                 __opcode 3 2)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
    then
      (do
        let w__1086 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__1086 <b 2740) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1087 : Bool)
  then
    (do
      writeReg SEE 2740
      let i2 := (BitVec.slice __opcode 16 2)
      let size := (BitVec.slice __opcode 12 2)
      let Zn := (BitVec.slice __opcode 5 5)
      let D := (BitVec.slice __opcode 4 1)
      let Zd := (BitVec.slice __opcode 0 2)
      (decode_LUTI2_MZ4_ZTZ_4 i2 size Zn D Zd)
      (pure false))
  else
    (do
      let w__1089 ← (( do
        if (((((Sail.BitVec.castWidth (m := 15) (Sail.BitVec.extractLsb __opcode 31 17)) == (0b110000001001101#15 : (BitVec 15))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                   __opcode 15 14)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                     __opcode 11 10)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                     __opcode 3 2)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
        then
          (do
            let w__1088 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__1088 <b 2741) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1089 : Bool)
      then
        (do
          writeReg SEE 2741
          let i1 := (BitVec.slice __opcode 16 1)
          let size := (BitVec.slice __opcode 12 2)
          let Zn := (BitVec.slice __opcode 5 5)
          let D := (BitVec.slice __opcode 4 1)
          let Zd := (BitVec.slice __opcode 0 2)
          (decode_LUTI4_MZ4_ZTZ_4 i1 size Zn D Zd)
          (pure false))
      else
        (do
          let w__1091 ← (( do
            if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb __opcode 31 16)) == (0xC002#16 : (BitVec 16))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                     __opcode 12 9)) == (0x1#4 : (BitVec 4)))) : Bool) : Bool)
            then
              (do
                let w__1090 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__1090 <b 2742) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__1091 : Bool)
          then
            (do
              writeReg SEE 2742
              let size := (BitVec.slice __opcode 22 2)
              let Q := (BitVec.slice __opcode 16 1)
              let V := (BitVec.slice __opcode 15 1)
              let Rs := (BitVec.slice __opcode 13 2)
              let off4 := (BitVec.slice __opcode 5 4)
              let Zd := (BitVec.slice __opcode 0 5)
              (decode_MOVAZ_Z_RZA_B size Q V Rs off4 Zd)
              (pure false))
          else
            (do
              let w__1093 ← (( do
                if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb __opcode 31 16)) == (0xC042#16 : (BitVec 16))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                         __opcode 12 9)) == (0x1#4 : (BitVec 4)))) : Bool) : Bool)
                then
                  (do
                    let w__1092 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__1092 <b 2743) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__1093 : Bool)
              then
                (do
                  writeReg SEE 2743
                  let size := (BitVec.slice __opcode 22 2)
                  let Q := (BitVec.slice __opcode 16 1)
                  let V := (BitVec.slice __opcode 15 1)
                  let Rs := (BitVec.slice __opcode 13 2)
                  let ZAn := (BitVec.slice __opcode 8 1)
                  let off3 := (BitVec.slice __opcode 5 3)
                  let Zd := (BitVec.slice __opcode 0 5)
                  (decode_MOVAZ_Z_RZA_H size Q V Rs ZAn off3 Zd)
                  (pure false))
              else
                (do
                  let w__1095 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb __opcode 31 16)) == (0xC082#16 : (BitVec 16))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                             __opcode 12 9)) == (0x1#4 : (BitVec 4)))) : Bool) : Bool)
                    then
                      (do
                        let w__1094 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__1094 <b 2744) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__1095 : Bool)
                  then
                    (do
                      writeReg SEE 2744
                      let size := (BitVec.slice __opcode 22 2)
                      let Q := (BitVec.slice __opcode 16 1)
                      let V := (BitVec.slice __opcode 15 1)
                      let Rs := (BitVec.slice __opcode 13 2)
                      let ZAn := (BitVec.slice __opcode 7 2)
                      let off2 := (BitVec.slice __opcode 5 2)
                      let Zd := (BitVec.slice __opcode 0 5)
                      (decode_MOVAZ_Z_RZA_W size Q V Rs ZAn off2 Zd)
                      (pure false))
                  else
                    (do
                      let w__1097 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb __opcode 31
                                 16)) == (0xC0C2#16 : (BitVec 16))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                 __opcode 12 9)) == (0x1#4 : (BitVec 4)))) : Bool) : Bool)
                        then
                          (do
                            let w__1096 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__1096 <b 2745) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__1097 : Bool)
                      then
                        (do
                          writeReg SEE 2745
                          let size := (BitVec.slice __opcode 22 2)
                          let Q := (BitVec.slice __opcode 16 1)
                          let V := (BitVec.slice __opcode 15 1)
                          let Rs := (BitVec.slice __opcode 13 2)
                          let ZAn := (BitVec.slice __opcode 6 3)
                          let o1 := (BitVec.slice __opcode 5 1)
                          let Zd := (BitVec.slice __opcode 0 5)
                          (decode_MOVAZ_Z_RZA_D size Q V Rs ZAn o1 Zd)
                          (pure false))
                      else
                        (do
                          let w__1099 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb __opcode
                                     31 16)) == (0xC0C3#16 : (BitVec 16))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                     __opcode 12 9)) == (0x1#4 : (BitVec 4)))) : Bool) : Bool)
                            then
                              (do
                                let w__1098 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__1098 <b 2746) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__1099 : Bool)
                          then
                            (do
                              writeReg SEE 2746
                              let size := (BitVec.slice __opcode 22 2)
                              let Q := (BitVec.slice __opcode 16 1)
                              let V := (BitVec.slice __opcode 15 1)
                              let Rs := (BitVec.slice __opcode 13 2)
                              let ZAn := (BitVec.slice __opcode 5 4)
                              let Zd := (BitVec.slice __opcode 0 5)
                              (decode_MOVAZ_Z_RZA_Q size Q V Rs ZAn Zd)
                              (pure false))
                          else
                            (do
                              let w__1101 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                         __opcode 31 16)) == (0xC006#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                           __opcode 12 8)) == (0b00010#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 0 0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__1100 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__1100 <b 2747) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__1101 : Bool)
                              then
                                (do
                                  writeReg SEE 2747
                                  let size := (BitVec.slice __opcode 22 2)
                                  let V := (BitVec.slice __opcode 15 1)
                                  let Rs := (BitVec.slice __opcode 13 2)
                                  let off3 := (BitVec.slice __opcode 5 3)
                                  let Zd := (BitVec.slice __opcode 1 4)
                                  (decode_MOVAZ_MZ2_ZA_B1 size V Rs off3 Zd)
                                  (pure false))
                              else
                                (do
                                  let w__1103 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                             __opcode 31 16)) == (0xC046#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                               __opcode 12 8)) == (0b00010#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 0 0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__1102 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__1102 <b 2748) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__1103 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2748
                                      let size := (BitVec.slice __opcode 22 2)
                                      let V := (BitVec.slice __opcode 15 1)
                                      let Rs := (BitVec.slice __opcode 13 2)
                                      let ZAn := (BitVec.slice __opcode 7 1)
                                      let off2 := (BitVec.slice __opcode 5 2)
                                      let Zd := (BitVec.slice __opcode 1 4)
                                      (decode_MOVAZ_MZ2_ZA_H1 size V Rs ZAn off2 Zd)
                                      (pure false))
                                  else
                                    (do
                                      let w__1105 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                 __opcode 31 16)) == (0xC086#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                   __opcode 12 8)) == (0b00010#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                   __opcode 0 0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__1104 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__1104 <b 2749) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__1105 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2749
                                          let size := (BitVec.slice __opcode 22 2)
                                          let V := (BitVec.slice __opcode 15 1)
                                          let Rs := (BitVec.slice __opcode 13 2)
                                          let ZAn := (BitVec.slice __opcode 6 2)
                                          let o1 := (BitVec.slice __opcode 5 1)
                                          let Zd := (BitVec.slice __opcode 1 4)
                                          (decode_MOVAZ_MZ2_ZA_W1 size V Rs ZAn o1 Zd)
                                          (pure false))
                                      else
                                        (do
                                          let w__1107 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                     __opcode 31 16)) == (0xC0C6#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                       __opcode 12 8)) == (0b00010#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 0 0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__1106 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__1106 <b 2750) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__1107 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2750
                                              let size := (BitVec.slice __opcode 22 2)
                                              let V := (BitVec.slice __opcode 15 1)
                                              let Rs := (BitVec.slice __opcode 13 2)
                                              let ZAn := (BitVec.slice __opcode 5 3)
                                              let Zd := (BitVec.slice __opcode 1 4)
                                              (decode_MOVAZ_MZ2_ZA_D1 size V Rs ZAn Zd)
                                              (pure false))
                                          else
                                            (do
                                              let w__1109 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                         __opcode 31 16)) == (0xC006#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                           __opcode 12 7)) == (0b001100#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                           __opcode 1 0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__1108 ← (( do readReg SEE ) : SailM Int
                                                      )
                                                    (pure (((w__1108 <b 2751) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__1109 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2751
                                                  let size := (BitVec.slice __opcode 22 2)
                                                  let V := (BitVec.slice __opcode 15 1)
                                                  let Rs := (BitVec.slice __opcode 13 2)
                                                  let off2 := (BitVec.slice __opcode 5 2)
                                                  let Zd := (BitVec.slice __opcode 2 3)
                                                  (decode_MOVAZ_MZ4_ZA_B1 size V Rs off2 Zd)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__1111 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                             __opcode 31 16)) == (0xC046#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                               __opcode 12 7)) == (0b001100#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                               __opcode 1 0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__1110 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__1110 <b 2752) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__1111 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2752
                                                      let size := (BitVec.slice __opcode 22 2)
                                                      let V := (BitVec.slice __opcode 15 1)
                                                      let Rs := (BitVec.slice __opcode 13 2)
                                                      let ZAn := (BitVec.slice __opcode 6 1)
                                                      let o1 := (BitVec.slice __opcode 5 1)
                                                      let Zd := (BitVec.slice __opcode 2 3)
                                                      (decode_MOVAZ_MZ4_ZA_H1 size V Rs ZAn o1 Zd)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__1113 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                 __opcode 31 16)) == (0xC086#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                   __opcode 12 7)) == (0b001100#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                   __opcode 1 0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__1112 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__1112 <b 2753) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__1113 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2753
                                                          let size := (BitVec.slice __opcode 22 2)
                                                          let V := (BitVec.slice __opcode 15 1)
                                                          let Rs := (BitVec.slice __opcode 13 2)
                                                          let ZAn := (BitVec.slice __opcode 5 2)
                                                          let Zd := (BitVec.slice __opcode 2 3)
                                                          (decode_MOVAZ_MZ4_ZA_W1 size V Rs ZAn Zd)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__1115 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                     __opcode 31 16)) == (0xC0C6#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                       __opcode 12 8)) == (0b00110#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                       __opcode 1 0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__1114 ← (( do readReg SEE )
                                                                  : SailM Int )
                                                                (pure (((w__1114 <b 2754) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__1115 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2754
                                                              let size :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let V := (BitVec.slice __opcode 15 1)
                                                              let Rs := (BitVec.slice __opcode 13 2)
                                                              let ZAn := (BitVec.slice __opcode 5 3)
                                                              let Zd := (BitVec.slice __opcode 2 3)
                                                              (decode_MOVAZ_MZ4_ZA_D1 size V Rs ZAn
                                                                Zd)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__1117 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                         __opcode 31 15)) == (0b11000000000001100#17 : (BitVec 17))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                           __opcode 12 8)) == (0b01010#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 0 0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__1116 ← (( do
                                                                      readReg SEE ) : SailM Int )
                                                                    (pure (((w__1116 <b 2755) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__1117 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2755
                                                                  let Rv :=
                                                                    (BitVec.slice __opcode 13 2)
                                                                  let off3 :=
                                                                    (BitVec.slice __opcode 5 3)
                                                                  let Zd :=
                                                                    (BitVec.slice __opcode 1 4)
                                                                  (decode_MOVAZ_MZ_ZA2_1 Rv off3 Zd)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__1119 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                             __opcode 31 15)) == (0b11000000000001100#17 : (BitVec 17))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                               __opcode 12 8)) == (0b01110#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                               __opcode 1 0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__1118 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__1118 <b 2756) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__1119 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2756
                                                                      let Rv :=
                                                                        (BitVec.slice __opcode 13 2)
                                                                      let off3 :=
                                                                        (BitVec.slice __opcode 5 3)
                                                                      let Zd :=
                                                                        (BitVec.slice __opcode 2 3)
                                                                      (decode_MOVAZ_MZ_ZA4_1 Rv off3
                                                                        Zd)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__1121 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 21)) == (0b10000001100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                 __opcode 4 1)) == (0x4#4 : (BitVec 4)))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__1120 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__1120 <b 2757) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__1121 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2757
                                                                          let Zm :=
                                                                            (BitVec.slice __opcode
                                                                              16 5)
                                                                          let Pm :=
                                                                            (BitVec.slice __opcode
                                                                              13 3)
                                                                          let Pn :=
                                                                            (BitVec.slice __opcode
                                                                              10 3)
                                                                          let Zn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let S :=
                                                                            (BitVec.slice __opcode 4
                                                                              1)
                                                                          let ZAda :=
                                                                            (BitVec.slice __opcode 0
                                                                              1)
                                                                          (decode_FMOPA_ZA_PP_ZZ_16
                                                                            Zm Pm Pn Zn S ZAda)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__1123 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 21)) == (0b10000001100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                     __opcode 4 1)) == (0xC#4 : (BitVec 4)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__1122 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__1122 <b 2758) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__1123 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2758
                                                                              let Zm :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 5)
                                                                              let Pm :=
                                                                                (BitVec.slice
                                                                                  __opcode 13 3)
                                                                              let Pn :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 3)
                                                                              let Zn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let S :=
                                                                                (BitVec.slice
                                                                                  __opcode 4 1)
                                                                              let ZAda :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 1)
                                                                              (decode_FMOPS_ZA_PP_ZZ_16
                                                                                Zm Pm Pn Zn S ZAda)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__1125 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         21)) == (0b10000001101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                         __opcode 4
                                                                                         1)) == (0x4#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__1124 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__1124 <b 2759) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__1125 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2759
                                                                                  let Zm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 5)
                                                                                  let Pm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 13 3)
                                                                                  let Pn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 3)
                                                                                  let Zn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let S :=
                                                                                    (BitVec.slice
                                                                                      __opcode 4 1)
                                                                                  let ZAda :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 1)
                                                                                  (decode_BFMOPA_ZA_PP_ZZ_16
                                                                                    Zm Pm Pn Zn S
                                                                                    ZAda)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__1127 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 21)) == (0b10000001101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             4 1)) == (0xC#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__1126 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__1126 <b 2760) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__1127 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2760
                                                                                      let Zm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 5)
                                                                                      let Pm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          13 3)
                                                                                      let Pn :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 3)
                                                                                      let Zn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let S :=
                                                                                        (BitVec.slice
                                                                                          __opcode 4
                                                                                          1)
                                                                                      let ZAda :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          1)
                                                                                      (decode_BFMOPS_ZA_PP_ZZ_16
                                                                                        Zm Pm Pn Zn
                                                                                        S ZAda)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__1129 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 15)) == (0b11000001101001000#17 : (BitVec 17))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   12
                                                                                                   10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   5
                                                                                                   3)) == (0b000#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__1128 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__1128 <b 2761) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__1129 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2761
                                                                                          let sz :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let Rv :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              13 2)
                                                                                          let Zm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              6 4)
                                                                                          let S :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              3 1)
                                                                                          let off3 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 3)
                                                                                          (decode_FADD_ZA_ZW_2x2_16
                                                                                            sz Rv Zm
                                                                                            S off3)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__1131 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     15)) == (0b11000001101001000#17 : (BitVec 17))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       12
                                                                                                       10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       5
                                                                                                       3)) == (0b001#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__1130 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__1130 <b 2762) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__1131 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2762
                                                                                              let sz :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  1)
                                                                                              let Rv :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  13
                                                                                                  2)
                                                                                              let Zm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  6
                                                                                                  4)
                                                                                              let S :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  3
                                                                                                  1)
                                                                                              let off3 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  3)
                                                                                              (decode_FSUB_ZA_ZW_2x2_16
                                                                                                sz
                                                                                                Rv
                                                                                                Zm S
                                                                                                off3)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__1133 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         15)) == (0b11000001111001000#17 : (BitVec 17))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           12
                                                                                                           10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           5
                                                                                                           3)) == (0b000#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__1132 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__1132 <b 2763) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__1133 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2763
                                                                                                  let sz :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      1)
                                                                                                  let Rv :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      13
                                                                                                      2)
                                                                                                  let Zm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      6
                                                                                                      4)
                                                                                                  let S :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      3
                                                                                                      1)
                                                                                                  let off3 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      3)
                                                                                                  (decode_BFADD_ZA_ZW_2x2_16
                                                                                                    sz
                                                                                                    Rv
                                                                                                    Zm
                                                                                                    S
                                                                                                    off3)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__1135 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             15)) == (0b11000001111001000#17 : (BitVec 17))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               12
                                                                                                               10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               5
                                                                                                               3)) == (0b001#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__1134 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__1134 <b 2764) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__1135 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 2764
                                                                                                      let sz :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          1)
                                                                                                      let Rv :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          13
                                                                                                          2)
                                                                                                      let Zm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          6
                                                                                                          4)
                                                                                                      let S :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          3
                                                                                                          1)
                                                                                                      let off3 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          3)
                                                                                                      (decode_BFSUB_ZA_ZW_2x2_16
                                                                                                        sz
                                                                                                        Rv
                                                                                                        Zm
                                                                                                        S
                                                                                                        off3)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__1137 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 15)) == (0b11000001101001010#17 : (BitVec 17))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   12
                                                                                                                   10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   6
                                                                                                                   3)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__1136 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__1136 <b 2765) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__1137 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 2765
                                                                                                          let sz :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              1)
                                                                                                          let Rv :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              13
                                                                                                              2)
                                                                                                          let Zm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              7
                                                                                                              3)
                                                                                                          let S :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              3
                                                                                                              1)
                                                                                                          let off3 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              3)
                                                                                                          (decode_FADD_ZA_ZW_4x4_16
                                                                                                            sz
                                                                                                            Rv
                                                                                                            Zm
                                                                                                            S
                                                                                                            off3)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__1139 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     15)) == (0b11000001101001010#17 : (BitVec 17))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       12
                                                                                                                       10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       6
                                                                                                                       3)) == (0x1#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__1138 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__1138 <b 2766) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__1139 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 2766
                                                                                                              let sz :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  1)
                                                                                                              let Rv :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  13
                                                                                                                  2)
                                                                                                              let Zm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  7
                                                                                                                  3)
                                                                                                              let S :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  3
                                                                                                                  1)
                                                                                                              let off3 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  3)
                                                                                                              (decode_FSUB_ZA_ZW_4x4_16
                                                                                                                sz
                                                                                                                Rv
                                                                                                                Zm
                                                                                                                S
                                                                                                                off3)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__1141 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         15)) == (0b11000001111001010#17 : (BitVec 17))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           12
                                                                                                                           10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           6
                                                                                                                           3)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__1140 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__1140 <b 2767) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__1141 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 2767
                                                                                                                  let sz :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      1)
                                                                                                                  let Rv :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      13
                                                                                                                      2)
                                                                                                                  let Zm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      7
                                                                                                                      3)
                                                                                                                  let S :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      3
                                                                                                                      1)
                                                                                                                  let off3 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      3)
                                                                                                                  (decode_BFADD_ZA_ZW_4x4_16
                                                                                                                    sz
                                                                                                                    Rv
                                                                                                                    Zm
                                                                                                                    S
                                                                                                                    off3)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__1143 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             15)) == (0b11000001111001010#17 : (BitVec 17))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               12
                                                                                                                               10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               6
                                                                                                                               3)) == (0x1#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__1142 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__1142 <b 2768) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__1143 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 2768
                                                                                                                      let sz :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          1)
                                                                                                                      let Rv :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          13
                                                                                                                          2)
                                                                                                                      let Zm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          7
                                                                                                                          3)
                                                                                                                      let S :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          3
                                                                                                                          1)
                                                                                                                      let off3 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          3)
                                                                                                                      (decode_BFSUB_ZA_ZW_4x4_16
                                                                                                                        sz
                                                                                                                        Rv
                                                                                                                        Zm
                                                                                                                        S
                                                                                                                        off3)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__1145 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 21)) == (0b11000001101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   16
                                                                                                                                   15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     12
                                                                                                                                     10)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     5
                                                                                                                                     3)) == (0b001#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__1144 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__1144 <b 2769) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__1145 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 2769
                                                                                                                          let sz :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              1)
                                                                                                                          let Zm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              17
                                                                                                                              4)
                                                                                                                          let Rv :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              13
                                                                                                                              2)
                                                                                                                          let Zn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              6
                                                                                                                              4)
                                                                                                                          let S :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              4
                                                                                                                              1)
                                                                                                                          let off3 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              3)
                                                                                                                          (decode_FMLA_ZA_ZZW_2x2_16
                                                                                                                            sz
                                                                                                                            Zm
                                                                                                                            Rv
                                                                                                                            Zn
                                                                                                                            S
                                                                                                                            off3)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__1147 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     21)) == (0b11000001101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       16
                                                                                                                                       15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         12
                                                                                                                                         10)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         5
                                                                                                                                         3)) == (0b011#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__1146 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__1146 <b 2770) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__1147 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 2770
                                                                                                                              let sz :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  1)
                                                                                                                              let Zm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  17
                                                                                                                                  4)
                                                                                                                              let Rv :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  13
                                                                                                                                  2)
                                                                                                                              let Zn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  6
                                                                                                                                  4)
                                                                                                                              let S :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  4
                                                                                                                                  1)
                                                                                                                              let off3 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  3)
                                                                                                                              (decode_FMLS_ZA_ZZW_2x2_16
                                                                                                                                sz
                                                                                                                                Zm
                                                                                                                                Rv
                                                                                                                                Zn
                                                                                                                                S
                                                                                                                                off3)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__1149 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         21)) == (0b11000001111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           16
                                                                                                                                           15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             12
                                                                                                                                             10)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             5
                                                                                                                                             3)) == (0b001#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__1148 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__1148 <b 2771) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__1149 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 2771
                                                                                                                                  let sz :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      1)
                                                                                                                                  let Zm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      17
                                                                                                                                      4)
                                                                                                                                  let Rv :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      13
                                                                                                                                      2)
                                                                                                                                  let Zn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      6
                                                                                                                                      4)
                                                                                                                                  let S :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      4
                                                                                                                                      1)
                                                                                                                                  let off3 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      3)
                                                                                                                                  (decode_BFMLA_ZA_ZZW_2x2_16
                                                                                                                                    sz
                                                                                                                                    Zm
                                                                                                                                    Rv
                                                                                                                                    Zn
                                                                                                                                    S
                                                                                                                                    off3)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__1151 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             21)) == (0b11000001111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               16
                                                                                                                                               15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 12
                                                                                                                                                 10)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 5
                                                                                                                                                 3)) == (0b011#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__1150 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__1150 <b 2772) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__1151 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 2772
                                                                                                                                      let sz :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          1)
                                                                                                                                      let Zm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          17
                                                                                                                                          4)
                                                                                                                                      let Rv :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          13
                                                                                                                                          2)
                                                                                                                                      let Zn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          6
                                                                                                                                          4)
                                                                                                                                      let S :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          4
                                                                                                                                          1)
                                                                                                                                      let off3 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          3)
                                                                                                                                      (decode_BFMLS_ZA_ZZW_2x2_16
                                                                                                                                        sz
                                                                                                                                        Zm
                                                                                                                                        Rv
                                                                                                                                        Zn
                                                                                                                                        S
                                                                                                                                        off3)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__1153 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 20)) == (0xC12#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   15
                                                                                                                                                   15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     12
                                                                                                                                                     10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     4
                                                                                                                                                     3)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__1152 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__1152 <b 2773) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__1153 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 2773
                                                                                                                                          let sz :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              22
                                                                                                                                              1)
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
                                                                                                                                          let Zn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              5)
                                                                                                                                          let S :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              3
                                                                                                                                              1)
                                                                                                                                          let off3 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              3)
                                                                                                                                          (decode_FMLA_ZA_ZZV_2x1_16
                                                                                                                                            sz
                                                                                                                                            Zm
                                                                                                                                            Rv
                                                                                                                                            Zn
                                                                                                                                            S
                                                                                                                                            off3)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__1155 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     20)) == (0xC12#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       15
                                                                                                                                                       15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         12
                                                                                                                                                         10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         4
                                                                                                                                                         3)) == (0b01#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__1154 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__1154 <b 2774) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__1155 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 2774
                                                                                                                                              let sz :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  22
                                                                                                                                                  1)
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
                                                                                                                                              let Zn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  5
                                                                                                                                                  5)
                                                                                                                                              let S :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  3
                                                                                                                                                  1)
                                                                                                                                              let off3 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  3)
                                                                                                                                              (decode_FMLS_ZA_ZZV_2x1_16
                                                                                                                                                sz
                                                                                                                                                Zm
                                                                                                                                                Rv
                                                                                                                                                Zn
                                                                                                                                                S
                                                                                                                                                off3)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__1157 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         20)) == (0xC16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           15
                                                                                                                                                           15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             12
                                                                                                                                                             10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             4
                                                                                                                                                             3)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__1156 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__1156 <b 2775) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__1157 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 2775
                                                                                                                                                  let sz :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      22
                                                                                                                                                      1)
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
                                                                                                                                                  let Zn :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      5
                                                                                                                                                      5)
                                                                                                                                                  let S :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      3
                                                                                                                                                      1)
                                                                                                                                                  let off3 :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      3)
                                                                                                                                                  (decode_BFMLA_ZA_ZZV_2x1_16
                                                                                                                                                    sz
                                                                                                                                                    Zm
                                                                                                                                                    Rv
                                                                                                                                                    Zn
                                                                                                                                                    S
                                                                                                                                                    off3)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__1159 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             20)) == (0xC16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               15
                                                                                                                                                               15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 12
                                                                                                                                                                 10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 4
                                                                                                                                                                 3)) == (0b01#2 : (BitVec 2)))))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__1158 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__1158 <b 2776) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__1159 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 2776
                                                                                                                                                      let sz :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          22
                                                                                                                                                          1)
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
                                                                                                                                                      let Zn :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          5
                                                                                                                                                          5)
                                                                                                                                                      let S :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          3
                                                                                                                                                          1)
                                                                                                                                                      let off3 :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          3)
                                                                                                                                                      (decode_BFMLS_ZA_ZZV_2x1_16
                                                                                                                                                        sz
                                                                                                                                                        Zm
                                                                                                                                                        Rv
                                                                                                                                                        Zn
                                                                                                                                                        S
                                                                                                                                                        off3)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__1161 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 21)) == (0b11000001101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   17
                                                                                                                                                                   15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     12
                                                                                                                                                                     10)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     6
                                                                                                                                                                     3)) == (0x1#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__1160 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__1160 <b 2777) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__1161 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 2777
                                                                                                                                                          let sz :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              22
                                                                                                                                                              1)
                                                                                                                                                          let Zm :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              18
                                                                                                                                                              3)
                                                                                                                                                          let Rv :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              13
                                                                                                                                                              2)
                                                                                                                                                          let Zn :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              7
                                                                                                                                                              3)
                                                                                                                                                          let S :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              4
                                                                                                                                                              1)
                                                                                                                                                          let off3 :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              0
                                                                                                                                                              3)
                                                                                                                                                          (decode_FMLA_ZA_ZZW_4x4_16
                                                                                                                                                            sz
                                                                                                                                                            Zm
                                                                                                                                                            Rv
                                                                                                                                                            Zn
                                                                                                                                                            S
                                                                                                                                                            off3)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (pure true))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
