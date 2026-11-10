import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1169
import ArmFull.Fn.M1170
import ArmFull.Fn.M1171

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
def __DecodeA64_SME__seg16 (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  let w__1163 ← (( do
    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11000001101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
               __opcode 17 15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                 __opcode 12 10)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                 __opcode 6 3)) == (0x3#4 : (BitVec 4)))))) : Bool) : Bool)
    then
      (do
        let w__1162 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__1162 <b 2778) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1163 : Bool)
  then
    (do
      writeReg SEE 2778
      let sz := (BitVec.slice __opcode 22 1)
      let Zm := (BitVec.slice __opcode 18 3)
      let Rv := (BitVec.slice __opcode 13 2)
      let Zn := (BitVec.slice __opcode 7 3)
      let S := (BitVec.slice __opcode 4 1)
      let off3 := (BitVec.slice __opcode 0 3)
      (decode_FMLS_ZA_ZZW_4x4_16 sz Zm Rv Zn S off3))
  else
    (do
      let w__1165 ← (( do
        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11000001111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                   __opcode 17 15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                     __opcode 12 10)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                     __opcode 6 3)) == (0x1#4 : (BitVec 4)))))) : Bool) : Bool)
        then
          (do
            let w__1164 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__1164 <b 2779) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1165 : Bool)
      then
        (do
          writeReg SEE 2779
          let sz := (BitVec.slice __opcode 22 1)
          let Zm := (BitVec.slice __opcode 18 3)
          let Rv := (BitVec.slice __opcode 13 2)
          let Zn := (BitVec.slice __opcode 7 3)
          let S := (BitVec.slice __opcode 4 1)
          let off3 := (BitVec.slice __opcode 0 3)
          (decode_BFMLA_ZA_ZZW_4x4_16 sz Zm Rv Zn S off3))
      else
        (do
          let w__1167 ← (( do
            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11000001111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                       __opcode 17 15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                         __opcode 12 10)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                         __opcode 6 3)) == (0x3#4 : (BitVec 4)))))) : Bool) : Bool)
            then
              (do
                let w__1166 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__1166 <b 2780) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__1167 : Bool)
          then
            (do
              writeReg SEE 2780
              let sz := (BitVec.slice __opcode 22 1)
              let Zm := (BitVec.slice __opcode 18 3)
              let Rv := (BitVec.slice __opcode 13 2)
              let Zn := (BitVec.slice __opcode 7 3)
              let S := (BitVec.slice __opcode 4 1)
              let off3 := (BitVec.slice __opcode 0 3)
              (decode_BFMLS_ZA_ZZW_4x4_16 sz Zm Rv Zn S off3))
          else
            (do
              let w__1169 ← (( do
                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xC13#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                             __opcode 12 10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                             __opcode 4 3)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                then
                  (do
                    let w__1168 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__1168 <b 2781) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__1169 : Bool)
              then
                (do
                  writeReg SEE 2781
                  let sz := (BitVec.slice __opcode 22 1)
                  let Zm := (BitVec.slice __opcode 16 4)
                  let Rv := (BitVec.slice __opcode 13 2)
                  let Zn := (BitVec.slice __opcode 5 5)
                  let S := (BitVec.slice __opcode 3 1)
                  let off3 := (BitVec.slice __opcode 0 3)
                  (decode_FMLA_ZA_ZZV_4x1_16 sz Zm Rv Zn S off3))
              else
                (do
                  let w__1171 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xC13#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                 __opcode 12 10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                 __opcode 4 3)) == (0b01#2 : (BitVec 2)))))) : Bool) : Bool)
                    then
                      (do
                        let w__1170 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__1170 <b 2782) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__1171 : Bool)
                  then
                    (do
                      writeReg SEE 2782
                      let sz := (BitVec.slice __opcode 22 1)
                      let Zm := (BitVec.slice __opcode 16 4)
                      let Rv := (BitVec.slice __opcode 13 2)
                      let Zn := (BitVec.slice __opcode 5 5)
                      let S := (BitVec.slice __opcode 3 1)
                      let off3 := (BitVec.slice __opcode 0 3)
                      (decode_FMLS_ZA_ZZV_4x1_16 sz Zm Rv Zn S off3))
                  else
                    (do
                      let w__1173 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31
                                 20)) == (0xC17#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                     __opcode 12 10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                     __opcode 4 3)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                        then
                          (do
                            let w__1172 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__1172 <b 2783) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__1173 : Bool)
                      then
                        (do
                          writeReg SEE 2783
                          let sz := (BitVec.slice __opcode 22 1)
                          let Zm := (BitVec.slice __opcode 16 4)
                          let Rv := (BitVec.slice __opcode 13 2)
                          let Zn := (BitVec.slice __opcode 5 5)
                          let S := (BitVec.slice __opcode 3 1)
                          let off3 := (BitVec.slice __opcode 0 3)
                          (decode_BFMLA_ZA_ZZV_4x1_16 sz Zm Rv Zn S off3))
                      else
                        (do
                          let w__1175 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode
                                     31 20)) == (0xC17#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                         __opcode 12 10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                         __opcode 4 3)) == (0b01#2 : (BitVec 2)))))) : Bool) : Bool)
                            then
                              (do
                                let w__1174 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__1174 <b 2784) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__1175 : Bool)
                          then
                            (do
                              writeReg SEE 2784
                              let sz := (BitVec.slice __opcode 22 1)
                              let Zm := (BitVec.slice __opcode 16 4)
                              let Rv := (BitVec.slice __opcode 13 2)
                              let Zn := (BitVec.slice __opcode 5 5)
                              let S := (BitVec.slice __opcode 3 1)
                              let off3 := (BitVec.slice __opcode 0 3)
                              (decode_BFMLS_ZA_ZZV_4x1_16 sz Zm Rv Zn S off3))
                          else
                            (do
                              let w__1177 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                         __opcode 31 20)) == (0xC11#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                           __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                             __opcode 5 4)) == (0b00#2 : (BitVec 2)))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__1176 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__1176 <b 2785) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__1177 : Bool)
                              then
                                (do
                                  writeReg SEE 2785
                                  let Zm := (BitVec.slice __opcode 16 4)
                                  let Rv := (BitVec.slice __opcode 13 2)
                                  let i3h := (BitVec.slice __opcode 10 2)
                                  let Zn := (BitVec.slice __opcode 6 4)
                                  let S := (BitVec.slice __opcode 4 1)
                                  let i3l := (BitVec.slice __opcode 3 1)
                                  let off3 := (BitVec.slice __opcode 0 3)
                                  (decode_FMLA_ZA_ZZi_H2xi Zm Rv i3h Zn S i3l off3))
                              else
                                (do
                                  let w__1179 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                             __opcode 31 20)) == (0xC11#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                 __opcode 5 4)) == (0b01#2 : (BitVec 2)))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__1178 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__1178 <b 2786) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__1179 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2786
                                      let Zm := (BitVec.slice __opcode 16 4)
                                      let Rv := (BitVec.slice __opcode 13 2)
                                      let i3h := (BitVec.slice __opcode 10 2)
                                      let Zn := (BitVec.slice __opcode 6 4)
                                      let S := (BitVec.slice __opcode 4 1)
                                      let i3l := (BitVec.slice __opcode 3 1)
                                      let off3 := (BitVec.slice __opcode 0 3)
                                      (decode_FMLS_ZA_ZZi_H2xi Zm Rv i3h Zn S i3l off3))
                                  else
                                    (do
                                      let w__1181 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                 __opcode 31 20)) == (0xC11#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                   __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                     __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                     __opcode 5 4)) == (0b10#2 : (BitVec 2)))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__1180 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__1180 <b 2787) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__1181 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2787
                                          let Zm := (BitVec.slice __opcode 16 4)
                                          let Rv := (BitVec.slice __opcode 13 2)
                                          let i3h := (BitVec.slice __opcode 10 2)
                                          let Zn := (BitVec.slice __opcode 6 4)
                                          let S := (BitVec.slice __opcode 4 1)
                                          let i3l := (BitVec.slice __opcode 3 1)
                                          let off3 := (BitVec.slice __opcode 0 3)
                                          (decode_BFMLA_ZA_ZZi_H2xi Zm Rv i3h Zn S i3l off3))
                                      else
                                        (do
                                          let w__1183 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                     __opcode 31 20)) == (0xC11#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 15 15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                         __opcode 5 4)) == (0b11#2 : (BitVec 2)))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__1182 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__1182 <b 2788) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__1183 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2788
                                              let Zm := (BitVec.slice __opcode 16 4)
                                              let Rv := (BitVec.slice __opcode 13 2)
                                              let i3h := (BitVec.slice __opcode 10 2)
                                              let Zn := (BitVec.slice __opcode 6 4)
                                              let S := (BitVec.slice __opcode 4 1)
                                              let i3l := (BitVec.slice __opcode 3 1)
                                              let off3 := (BitVec.slice __opcode 0 3)
                                              (decode_BFMLS_ZA_ZZi_H2xi Zm Rv i3h Zn S i3l off3))
                                          else
                                            (do
                                              let w__1185 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                         __opcode 31 20)) == (0xC11#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                             __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                             __opcode 6 4)) == (0b000#3 : (BitVec 3)))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__1184 ← (( do readReg SEE ) : SailM Int
                                                      )
                                                    (pure (((w__1184 <b 2789) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__1185 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2789
                                                  let Zm := (BitVec.slice __opcode 16 4)
                                                  let Rv := (BitVec.slice __opcode 13 2)
                                                  let i3h := (BitVec.slice __opcode 10 2)
                                                  let Zn := (BitVec.slice __opcode 7 3)
                                                  let S := (BitVec.slice __opcode 4 1)
                                                  let i3l := (BitVec.slice __opcode 3 1)
                                                  let off3 := (BitVec.slice __opcode 0 3)
                                                  (decode_FMLA_ZA_ZZi_H4xi Zm Rv i3h Zn S i3l off3))
                                              else
                                                (do
                                                  let w__1187 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                             __opcode 31 20)) == (0xC11#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                 __opcode 6 4)) == (0b001#3 : (BitVec 3)))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__1186 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__1186 <b 2790) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__1187 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2790
                                                      let Zm := (BitVec.slice __opcode 16 4)
                                                      let Rv := (BitVec.slice __opcode 13 2)
                                                      let i3h := (BitVec.slice __opcode 10 2)
                                                      let Zn := (BitVec.slice __opcode 7 3)
                                                      let S := (BitVec.slice __opcode 4 1)
                                                      let i3l := (BitVec.slice __opcode 3 1)
                                                      let off3 := (BitVec.slice __opcode 0 3)
                                                      (decode_FMLS_ZA_ZZi_H4xi Zm Rv i3h Zn S i3l
                                                        off3))
                                                  else
                                                    (do
                                                      let w__1189 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                 __opcode 31 20)) == (0xC11#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                     __opcode 6 4)) == (0b010#3 : (BitVec 3)))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__1188 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__1188 <b 2791) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__1189 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2791
                                                          let Zm := (BitVec.slice __opcode 16 4)
                                                          let Rv := (BitVec.slice __opcode 13 2)
                                                          let i3h := (BitVec.slice __opcode 10 2)
                                                          let Zn := (BitVec.slice __opcode 7 3)
                                                          let S := (BitVec.slice __opcode 4 1)
                                                          let i3l := (BitVec.slice __opcode 3 1)
                                                          let off3 := (BitVec.slice __opcode 0 3)
                                                          (decode_BFMLA_ZA_ZZi_H4xi Zm Rv i3h Zn S
                                                            i3l off3))
                                                      else
                                                        (do
                                                          let w__1191 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                     __opcode 31 20)) == (0xC11#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 15 15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 12 12)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                         __opcode 6 4)) == (0b011#3 : (BitVec 3)))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__1190 ← (( do readReg SEE )
                                                                  : SailM Int )
                                                                (pure (((w__1190 <b 2792) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__1191 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2792
                                                              let Zm := (BitVec.slice __opcode 16 4)
                                                              let Rv := (BitVec.slice __opcode 13 2)
                                                              let i3h :=
                                                                (BitVec.slice __opcode 10 2)
                                                              let Zn := (BitVec.slice __opcode 7 3)
                                                              let S := (BitVec.slice __opcode 4 1)
                                                              let i3l := (BitVec.slice __opcode 3 1)
                                                              let off3 :=
                                                                (BitVec.slice __opcode 0 3)
                                                              (decode_BFMLS_ZA_ZZi_H4xi Zm Rv i3h Zn
                                                                S i3l off3))
                                                          else
                                                            (do
                                                              let w__1193 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                         __opcode 31 21)) == (0b11000001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                           __opcode 16 5)) == (0x588#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 0 0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__1192 ← (( do
                                                                      readReg SEE ) : SailM Int )
                                                                    (pure (((w__1192 <b 2793) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__1193 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2793
                                                                  let size :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let Zm :=
                                                                    (BitVec.slice __opcode 17 4)
                                                                  let Zdn :=
                                                                    (BitVec.slice __opcode 1 4)
                                                                  (decode_BFMAX_MZ_ZZW_2x2 size Zm
                                                                    Zdn))
                                                              else
                                                                (do
                                                                  let w__1195 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                             __opcode 31 20)) == (0xC12#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                               __opcode 15 5)) == (0b10100001000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 0 0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__1194 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__1194 <b 2794) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__1195 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2794
                                                                      let size :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let Zm :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let Zdn :=
                                                                        (BitVec.slice __opcode 1 4)
                                                                      (decode_BFMAX_MZ_ZZV_2x1 size
                                                                        Zm Zdn))
                                                                  else
                                                                    (do
                                                                      let w__1197 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 21)) == (0b11000001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                   __opcode 16 5)) == (0x588#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 0 0)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__1196 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__1196 <b 2795) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__1197 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2795
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let Zm :=
                                                                            (BitVec.slice __opcode
                                                                              17 4)
                                                                          let Zdn :=
                                                                            (BitVec.slice __opcode 1
                                                                              4)
                                                                          (decode_BFMIN_MZ_ZZW_2x2
                                                                            size Zm Zdn))
                                                                      else
                                                                        (do
                                                                          let w__1199 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 20)) == (0xC12#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                       __opcode 15 5)) == (0b10100001000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 0 0)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__1198 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__1198 <b 2796) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__1199 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2796
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let Zm :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let Zdn :=
                                                                                (BitVec.slice
                                                                                  __opcode 1 4)
                                                                              (decode_BFMIN_MZ_ZZV_2x1
                                                                                size Zm Zdn))
                                                                          else
                                                                            (do
                                                                              let w__1201 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         21)) == (0b11000001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           17 5)) == (0b0010111001000#13 : (BitVec 13))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           1 0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__1200 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__1200 <b 2797) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__1201 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2797
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let Zm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 18 3)
                                                                                  let Zdn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 2 3)
                                                                                  (decode_BFMAX_MZ_ZZW_4x4
                                                                                    size Zm Zdn))
                                                                              else
                                                                                (do
                                                                                  let w__1203 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 20)) == (0xC12#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               15 5)) == (0b10101001000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               1 0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__1202 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__1202 <b 2798) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__1203 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2798
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 2)
                                                                                      let Zm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let Zdn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 2
                                                                                          3)
                                                                                      (decode_BFMAX_MZ_ZZV_4x1
                                                                                        size Zm Zdn))
                                                                                  else
                                                                                    (do
                                                                                      let w__1205 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 21)) == (0b11000001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   17
                                                                                                   5)) == (0b0010111001000#13 : (BitVec 13))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   1
                                                                                                   0)) == (0b01#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__1204 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__1204 <b 2799) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__1205 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2799
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 2)
                                                                                          let Zm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              18 3)
                                                                                          let Zdn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              2 3)
                                                                                          (decode_BFMIN_MZ_ZZW_4x4
                                                                                            size Zm
                                                                                            Zdn))
                                                                                      else
                                                                                        (do
                                                                                          let w__1207 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     20)) == (0xC12#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       15
                                                                                                       5)) == (0b10101001000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       1
                                                                                                       0)) == (0b01#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__1206 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__1206 <b 2800) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__1207 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2800
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
                                                                                                  2
                                                                                                  3)
                                                                                              (decode_BFMIN_MZ_ZZV_4x1
                                                                                                size
                                                                                                Zm
                                                                                                Zdn))
                                                                                          else
                                                                                            (do
                                                                                              let w__1209 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         21)) == (0b11000001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           16
                                                                                                           5)) == (0x589#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           0
                                                                                                           0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__1208 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__1208 <b 2801) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__1209 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2801
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
                                                                                                  (decode_BFMAXNM_MZ_ZZW_2x2
                                                                                                    size
                                                                                                    Zm
                                                                                                    Zdn))
                                                                                              else
                                                                                                (do
                                                                                                  let w__1211 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             20)) == (0xC12#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               5)) == (0b10100001001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               0
                                                                                                               0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__1210 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__1210 <b 2802) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__1211 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 2802
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
                                                                                                      (decode_BFMAXNM_MZ_ZZV_2x1
                                                                                                        size
                                                                                                        Zm
                                                                                                        Zdn))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__1213 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 21)) == (0b11000001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   16
                                                                                                                   5)) == (0x589#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   0
                                                                                                                   0)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__1212 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__1212 <b 2803) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__1213 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 2803
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
                                                                                                          (decode_BFMINNM_MZ_ZZW_2x2
                                                                                                            size
                                                                                                            Zm
                                                                                                            Zdn))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__1215 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     20)) == (0xC12#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       15
                                                                                                                       5)) == (0b10100001001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       0
                                                                                                                       0)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__1214 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__1214 <b 2804) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__1215 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 2804
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
                                                                                                              (decode_BFMINNM_MZ_ZZV_2x1
                                                                                                                size
                                                                                                                Zm
                                                                                                                Zdn))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__1217 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         21)) == (0b11000001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           17
                                                                                                                           5)) == (0b0010111001001#13 : (BitVec 13))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           1
                                                                                                                           0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__1216 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__1216 <b 2805) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__1217 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 2805
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
                                                                                                                  (decode_BFMAXNM_MZ_ZZW_4x4
                                                                                                                    size
                                                                                                                    Zm
                                                                                                                    Zdn))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__1219 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             20)) == (0xC12#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               15
                                                                                                                               5)) == (0b10101001001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               1
                                                                                                                               0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__1218 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__1218 <b 2806) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__1219 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 2806
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
                                                                                                                          2
                                                                                                                          3)
                                                                                                                      (decode_BFMAXNM_MZ_ZZV_4x1
                                                                                                                        size
                                                                                                                        Zm
                                                                                                                        Zdn))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__1221 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 21)) == (0b11000001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   17
                                                                                                                                   5)) == (0b0010111001001#13 : (BitVec 13))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   1
                                                                                                                                   0)) == (0b01#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__1220 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__1220 <b 2807) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__1221 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 2807
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
                                                                                                                          (decode_BFMINNM_MZ_ZZW_4x4
                                                                                                                            size
                                                                                                                            Zm
                                                                                                                            Zdn))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__1223 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     20)) == (0xC12#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       5)) == (0b10101001001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       1
                                                                                                                                       0)) == (0b01#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__1222 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__1222 <b 2808) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__1223 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 2808
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
                                                                                                                                  2
                                                                                                                                  3)
                                                                                                                              (decode_BFMINNM_MZ_ZZV_4x1
                                                                                                                                size
                                                                                                                                Zm
                                                                                                                                Zdn))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__1225 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         10)) == (0b1100000110100000111000#22 : (BitVec 22))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         0
                                                                                                                                         0)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__1224 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__1224 <b 2809) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__1225 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 2809
                                                                                                                                  let Zn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      5
                                                                                                                                      5)
                                                                                                                                  let Zd :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      1
                                                                                                                                      4)
                                                                                                                                  let L :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      1)
                                                                                                                                  (decode_FCVT_MZ2_Z__
                                                                                                                                    Zn
                                                                                                                                    Zd
                                                                                                                                    L))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__1227 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             10)) == (0b1100000110100000111000#22 : (BitVec 22))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             0
                                                                                                                                             0)) == (1#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__1226 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__1226 <b 2810) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__1227 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 2810
                                                                                                                                      let Zn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          5
                                                                                                                                          5)
                                                                                                                                      let Zd :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          1
                                                                                                                                          4)
                                                                                                                                      let L :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          1)
                                                                                                                                      (decode_FCVTL_MZ2_Z__
                                                                                                                                        Zn
                                                                                                                                        Zd
                                                                                                                                        L))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__1229 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 21)) == (0b11000001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   15
                                                                                                                                                   10)) == (0b110000#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   0
                                                                                                                                                   0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__1228 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__1228 <b 2811) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__1229 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 2811
                                                                                                                                          let size :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              22
                                                                                                                                              2)
                                                                                                                                          let Zm :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              5)
                                                                                                                                          let Zn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              5)
                                                                                                                                          let Zd :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              1
                                                                                                                                              4)
                                                                                                                                          (decode_BFCLAMP_MZ_ZZ_2
                                                                                                                                            size
                                                                                                                                            Zm
                                                                                                                                            Zn
                                                                                                                                            Zd))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__1231 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     21)) == (0b11000001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       15
                                                                                                                                                       10)) == (0b110010#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       1
                                                                                                                                                       0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__1230 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__1230 <b 2812) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__1231 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 2812
                                                                                                                                              let size :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  22
                                                                                                                                                  2)
                                                                                                                                              let Zm :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  5)
                                                                                                                                              let Zn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  5
                                                                                                                                                  5)
                                                                                                                                              let Zd :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  2
                                                                                                                                                  3)
                                                                                                                                              (decode_BFCLAMP_MZ_ZZ_4
                                                                                                                                                size
                                                                                                                                                Zm
                                                                                                                                                Zn
                                                                                                                                                Zd))
                                                                                                                                          else
                                                                                                                                            sailThrow ((Error_Undefined
                                                                                                                                              ()))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
