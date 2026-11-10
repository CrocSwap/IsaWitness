import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0898
import ArmFull.Fn.M0987
import ArmFull.Fn.M0988
import ArmFull.Fn.M1341
import ArmFull.Fn.M1342

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
def __DecodeA64_SME__seg3 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__221 ← (( do
    if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb __opcode 31 16)) == (0xC090#16 : (BitVec 16))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
             __opcode 4 2)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
    then
      (do
        let w__220 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__220 <b 2304) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__221 : Bool)
  then
    (do
      writeReg SEE 2304
      let V := (BitVec.slice __opcode 16 1)
      let Pm := (BitVec.slice __opcode 13 3)
      let Pn := (BitVec.slice __opcode 10 3)
      let Zn := (BitVec.slice __opcode 5 5)
      let ZAda := (BitVec.slice __opcode 0 2)
      (decode_ADDHA_ZA_PP_Z_32 V Pm Pn Zn ZAda)
      (pure false))
  else
    (do
      let w__223 ← (( do
        if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb __opcode 31 16)) == (0xC0D0#16 : (BitVec 16))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                 __opcode 4 3)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
        then
          (do
            let w__222 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__222 <b 2305) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__223 : Bool)
      then
        (do
          writeReg SEE 2305
          let V := (BitVec.slice __opcode 16 1)
          let Pm := (BitVec.slice __opcode 13 3)
          let Pn := (BitVec.slice __opcode 10 3)
          let Zn := (BitVec.slice __opcode 5 5)
          let ZAda := (BitVec.slice __opcode 0 3)
          (decode_ADDHA_ZA_PP_Z_64 V Pm Pn Zn ZAda)
          (pure false))
      else
        (do
          let w__225 ← (( do
            if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb __opcode 31 16)) == (0xC091#16 : (BitVec 16))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                     __opcode 4 2)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
            then
              (do
                let w__224 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__224 <b 2306) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__225 : Bool)
          then
            (do
              writeReg SEE 2306
              let V := (BitVec.slice __opcode 16 1)
              let Pm := (BitVec.slice __opcode 13 3)
              let Pn := (BitVec.slice __opcode 10 3)
              let Zn := (BitVec.slice __opcode 5 5)
              let ZAda := (BitVec.slice __opcode 0 2)
              (decode_ADDVA_ZA_PP_Z_32 V Pm Pn Zn ZAda)
              (pure false))
          else
            (do
              let w__227 ← (( do
                if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb __opcode 31 16)) == (0xC0D1#16 : (BitVec 16))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                         __opcode 4 3)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                then
                  (do
                    let w__226 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__226 <b 2307) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__227 : Bool)
              then
                (do
                  writeReg SEE 2307
                  let V := (BitVec.slice __opcode 16 1)
                  let Pm := (BitVec.slice __opcode 13 3)
                  let Pn := (BitVec.slice __opcode 10 3)
                  let Zn := (BitVec.slice __opcode 5 5)
                  let ZAda := (BitVec.slice __opcode 0 3)
                  (decode_ADDVA_ZA_PP_Z_64 V Pm Pn Zn ZAda)
                  (pure false))
              else
                (do
                  let w__229 ← (( do
                    if ((((Sail.BitVec.castWidth (m := 24) (Sail.BitVec.extractLsb __opcode 31 8)) == (0xC00800#24 : (BitVec 24))) : Bool) : Bool)
                    then
                      (do
                        let w__228 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__228 <b 2308) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__229 : Bool)
                  then
                    (do
                      writeReg SEE 2308
                      let imm8 := (BitVec.slice __opcode 0 8)
                      (decode_ZERO_ZA_I__ imm8)
                      (pure false))
                  else
                    (do
                      let w__231 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb __opcode 31
                                 16)) == (0xC004#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                   __opcode 12 10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                   __opcode 5 3)) == (0b000#3 : (BitVec 3))))) : Bool) : Bool)
                        then
                          (do
                            let w__230 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__230 <b 2309) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__231 : Bool)
                      then
                        (do
                          writeReg SEE 2309
                          let size := (BitVec.slice __opcode 22 2)
                          let V := (BitVec.slice __opcode 15 1)
                          let Rs := (BitVec.slice __opcode 13 2)
                          let Zn := (BitVec.slice __opcode 6 4)
                          let off3 := (BitVec.slice __opcode 0 3)
                          (decode_MOVA_ZA2_Z_B1 size V Rs Zn off3)
                          (pure false))
                      else
                        (do
                          let w__233 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb __opcode
                                     31 16)) == (0xC044#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                       __opcode 12 10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                       __opcode 5 3)) == (0b000#3 : (BitVec 3))))) : Bool) : Bool)
                            then
                              (do
                                let w__232 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__232 <b 2310) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__233 : Bool)
                          then
                            (do
                              writeReg SEE 2310
                              let size := (BitVec.slice __opcode 22 2)
                              let V := (BitVec.slice __opcode 15 1)
                              let Rs := (BitVec.slice __opcode 13 2)
                              let Zn := (BitVec.slice __opcode 6 4)
                              let ZAd := (BitVec.slice __opcode 2 1)
                              let off2 := (BitVec.slice __opcode 0 2)
                              (decode_MOVA_ZA2_Z_H1 size V Rs Zn ZAd off2)
                              (pure false))
                          else
                            (do
                              let w__235 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                         __opcode 31 16)) == (0xC084#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                           __opcode 12 10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                           __opcode 5 3)) == (0b000#3 : (BitVec 3))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__234 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__234 <b 2311) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__235 : Bool)
                              then
                                (do
                                  writeReg SEE 2311
                                  let size := (BitVec.slice __opcode 22 2)
                                  let V := (BitVec.slice __opcode 15 1)
                                  let Rs := (BitVec.slice __opcode 13 2)
                                  let Zn := (BitVec.slice __opcode 6 4)
                                  let ZAd := (BitVec.slice __opcode 1 2)
                                  let o1 := (BitVec.slice __opcode 0 1)
                                  (decode_MOVA_ZA2_Z_W1 size V Rs Zn ZAd o1)
                                  (pure false))
                              else
                                (do
                                  let w__237 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                             __opcode 31 16)) == (0xC0C4#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                               __opcode 12 10)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                               __opcode 5 3)) == (0b000#3 : (BitVec 3))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__236 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__236 <b 2312) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__237 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2312
                                      let size := (BitVec.slice __opcode 22 2)
                                      let V := (BitVec.slice __opcode 15 1)
                                      let Rs := (BitVec.slice __opcode 13 2)
                                      let Zn := (BitVec.slice __opcode 6 4)
                                      let ZAd := (BitVec.slice __opcode 0 3)
                                      (decode_MOVA_ZA2_Z_D1 size V Rs Zn ZAd)
                                      (pure false))
                                  else
                                    (do
                                      let w__239 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                 __opcode 31 16)) == (0xC004#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                   __opcode 12 10)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                   __opcode 6 2)) == (0b00000#5 : (BitVec 5))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__238 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__238 <b 2313) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__239 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2313
                                          let size := (BitVec.slice __opcode 22 2)
                                          let V := (BitVec.slice __opcode 15 1)
                                          let Rs := (BitVec.slice __opcode 13 2)
                                          let Zn := (BitVec.slice __opcode 7 3)
                                          let off2 := (BitVec.slice __opcode 0 2)
                                          (decode_MOVA_ZA4_Z_B1 size V Rs Zn off2)
                                          (pure false))
                                      else
                                        (do
                                          let w__241 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                     __opcode 31 16)) == (0xC044#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                       __opcode 12 10)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                       __opcode 6 2)) == (0b00000#5 : (BitVec 5))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__240 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__240 <b 2314) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__241 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2314
                                              let size := (BitVec.slice __opcode 22 2)
                                              let V := (BitVec.slice __opcode 15 1)
                                              let Rs := (BitVec.slice __opcode 13 2)
                                              let Zn := (BitVec.slice __opcode 7 3)
                                              let ZAd := (BitVec.slice __opcode 1 1)
                                              let o1 := (BitVec.slice __opcode 0 1)
                                              (decode_MOVA_ZA4_Z_H1 size V Rs Zn ZAd o1)
                                              (pure false))
                                          else
                                            (do
                                              let w__243 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                         __opcode 31 16)) == (0xC084#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                           __opcode 12 10)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                           __opcode 6 2)) == (0b00000#5 : (BitVec 5))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__242 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__242 <b 2315) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__243 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2315
                                                  let size := (BitVec.slice __opcode 22 2)
                                                  let V := (BitVec.slice __opcode 15 1)
                                                  let Rs := (BitVec.slice __opcode 13 2)
                                                  let Zn := (BitVec.slice __opcode 7 3)
                                                  let ZAd := (BitVec.slice __opcode 0 2)
                                                  (decode_MOVA_ZA4_Z_W1 size V Rs Zn ZAd)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__245 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                             __opcode 31 16)) == (0xC0C4#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                               __opcode 12 10)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                               __opcode 6 3)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__244 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__244 <b 2316) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__245 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2316
                                                      let size := (BitVec.slice __opcode 22 2)
                                                      let V := (BitVec.slice __opcode 15 1)
                                                      let Rs := (BitVec.slice __opcode 13 2)
                                                      let Zn := (BitVec.slice __opcode 7 3)
                                                      let ZAd := (BitVec.slice __opcode 0 3)
                                                      (decode_MOVA_ZA4_Z_D1 size V Rs Zn ZAd)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__247 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                 __opcode 31 15)) == (0b11000000000001000#17 : (BitVec 17))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                   __opcode 12 10)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                   __opcode 5 3)) == (0b000#3 : (BitVec 3))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__246 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__246 <b 2317) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__247 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2317
                                                          let Rv := (BitVec.slice __opcode 13 2)
                                                          let Zn := (BitVec.slice __opcode 6 4)
                                                          let off3 := (BitVec.slice __opcode 0 3)
                                                          (decode_MOVA_ZA_MZ2_1 Rv Zn off3)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__249 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                     __opcode 31 15)) == (0b11000000000001000#17 : (BitVec 17))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                       __opcode 12 10)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                       __opcode 6 3)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__248 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__248 <b 2318) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__249 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2318
                                                              let Rv := (BitVec.slice __opcode 13 2)
                                                              let Zn := (BitVec.slice __opcode 7 3)
                                                              let off3 :=
                                                                (BitVec.slice __opcode 0 3)
                                                              (decode_MOVA_ZA_MZ4_1 Rv Zn off3)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__251 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                         __opcode 31 16)) == (0xC006#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                           __opcode 12 8)) == (0b00000#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 0 0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__250 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__250 <b 2319) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__251 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2319
                                                                  let size :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let V :=
                                                                    (BitVec.slice __opcode 15 1)
                                                                  let Rs :=
                                                                    (BitVec.slice __opcode 13 2)
                                                                  let off3 :=
                                                                    (BitVec.slice __opcode 5 3)
                                                                  let Zd :=
                                                                    (BitVec.slice __opcode 1 4)
                                                                  (decode_MOVA_MZ2_ZA_B1 size V Rs
                                                                    off3 Zd)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__253 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                             __opcode 31 16)) == (0xC046#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                               __opcode 12 8)) == (0b00000#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 0 0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__252 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__252 <b 2320) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__253 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2320
                                                                      let size :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let V :=
                                                                        (BitVec.slice __opcode 15 1)
                                                                      let Rs :=
                                                                        (BitVec.slice __opcode 13 2)
                                                                      let ZAn :=
                                                                        (BitVec.slice __opcode 7 1)
                                                                      let off2 :=
                                                                        (BitVec.slice __opcode 5 2)
                                                                      let Zd :=
                                                                        (BitVec.slice __opcode 1 4)
                                                                      (decode_MOVA_MZ2_ZA_H1 size V
                                                                        Rs ZAn off2 Zd)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__255 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 16)) == (0xC086#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                   __opcode 12 8)) == (0b00000#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 0 0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__254 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__254 <b 2321) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__255 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2321
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let V :=
                                                                            (BitVec.slice __opcode
                                                                              15 1)
                                                                          let Rs :=
                                                                            (BitVec.slice __opcode
                                                                              13 2)
                                                                          let ZAn :=
                                                                            (BitVec.slice __opcode 6
                                                                              2)
                                                                          let o1 :=
                                                                            (BitVec.slice __opcode 5
                                                                              1)
                                                                          let Zd :=
                                                                            (BitVec.slice __opcode 1
                                                                              4)
                                                                          (decode_MOVA_MZ2_ZA_W1
                                                                            size V Rs ZAn o1 Zd)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__257 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 16)) == (0xC0C6#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                       __opcode 12 8)) == (0b00000#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 0 0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__256 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__256 <b 2322) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__257 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2322
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let V :=
                                                                                (BitVec.slice
                                                                                  __opcode 15 1)
                                                                              let Rs :=
                                                                                (BitVec.slice
                                                                                  __opcode 13 2)
                                                                              let ZAn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 3)
                                                                              let Zd :=
                                                                                (BitVec.slice
                                                                                  __opcode 1 4)
                                                                              (decode_MOVA_MZ2_ZA_D1
                                                                                size V Rs ZAn Zd)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__259 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         16)) == (0xC006#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           12 7)) == (0b001000#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           1 0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__258 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__258 <b 2323) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__259 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2323
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let V :=
                                                                                    (BitVec.slice
                                                                                      __opcode 15 1)
                                                                                  let Rs :=
                                                                                    (BitVec.slice
                                                                                      __opcode 13 2)
                                                                                  let off2 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 2)
                                                                                  let Zd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 2 3)
                                                                                  (decode_MOVA_MZ4_ZA_B1
                                                                                    size V Rs off2
                                                                                    Zd)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__261 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 16)) == (0xC046#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               12 7)) == (0b001000#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               1 0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__260 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__260 <b 2324) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__261 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2324
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 2)
                                                                                      let V :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          15 1)
                                                                                      let Rs :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          13 2)
                                                                                      let ZAn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 6
                                                                                          1)
                                                                                      let o1 :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          1)
                                                                                      let Zd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 2
                                                                                          3)
                                                                                      (decode_MOVA_MZ4_ZA_H1
                                                                                        size V Rs
                                                                                        ZAn o1 Zd)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__263 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 16)) == (0xC086#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   12
                                                                                                   7)) == (0b001000#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   1
                                                                                                   0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__262 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__262 <b 2325) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__263 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2325
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 2)
                                                                                          let V :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              15 1)
                                                                                          let Rs :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              13 2)
                                                                                          let ZAn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 2)
                                                                                          let Zd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              2 3)
                                                                                          (decode_MOVA_MZ4_ZA_W1
                                                                                            size V
                                                                                            Rs ZAn
                                                                                            Zd)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__265 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     16)) == (0xC0C6#16 : (BitVec 16))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       12
                                                                                                       8)) == (0b00100#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       1
                                                                                                       0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__264 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__264 <b 2326) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__265 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2326
                                                                                              let size :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  2)
                                                                                              let V :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  15
                                                                                                  1)
                                                                                              let Rs :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  13
                                                                                                  2)
                                                                                              let ZAn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  3)
                                                                                              let Zd :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  2
                                                                                                  3)
                                                                                              (decode_MOVA_MZ4_ZA_D1
                                                                                                size
                                                                                                V Rs
                                                                                                ZAn
                                                                                                Zd)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__267 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         15)) == (0b11000000000001100#17 : (BitVec 17))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           12
                                                                                                           8)) == (0b01000#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           0
                                                                                                           0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__266 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__266 <b 2327) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__267 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2327
                                                                                                  let Rv :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      13
                                                                                                      2)
                                                                                                  let off3 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      3)
                                                                                                  let Zd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      1
                                                                                                      4)
                                                                                                  (decode_MOVA_MZ_ZA2_1
                                                                                                    Rv
                                                                                                    off3
                                                                                                    Zd)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__269 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 17) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             15)) == (0b11000000000001100#17 : (BitVec 17))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               12
                                                                                                               8)) == (0b01100#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               1
                                                                                                               0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__268 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__268 <b 2328) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__269 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 2328
                                                                                                      let Rv :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          13
                                                                                                          2)
                                                                                                      let off3 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          3)
                                                                                                      let Zd :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          2
                                                                                                          3)
                                                                                                      (decode_MOVA_MZ_ZA4_1
                                                                                                        Rv
                                                                                                        off3
                                                                                                        Zd)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__271 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 21)) == (0b10100001000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   15
                                                                                                                   13)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   3
                                                                                                                   3)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__270 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__270 <b 2329) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__271 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 2329
                                                                                                          let Rm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              5)
                                                                                                          let msz :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              13
                                                                                                              2)
                                                                                                          let PNg :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              10
                                                                                                              3)
                                                                                                          let Rn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              5)
                                                                                                          let T :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              4
                                                                                                              1)
                                                                                                          let N :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              3
                                                                                                              1)
                                                                                                          let Zt :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              3)
                                                                                                          (decode_LD1B_MZx_P_BR_2x8
                                                                                                            Rm
                                                                                                            msz
                                                                                                            PNg
                                                                                                            Rn
                                                                                                            T
                                                                                                            N
                                                                                                            Zt)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__273 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     21)) == (0b10100001000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       15
                                                                                                                       13)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       3
                                                                                                                       3)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__272 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__272 <b 2330) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__273 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 2330
                                                                                                              let Rm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  5)
                                                                                                              let msz :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  13
                                                                                                                  2)
                                                                                                              let PNg :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  10
                                                                                                                  3)
                                                                                                              let Rn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  5)
                                                                                                              let T :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  4
                                                                                                                  1)
                                                                                                              let N :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  3
                                                                                                                  1)
                                                                                                              let Zt :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  3)
                                                                                                              (decode_LD1H_MZx_P_BR_2x8
                                                                                                                Rm
                                                                                                                msz
                                                                                                                PNg
                                                                                                                Rn
                                                                                                                T
                                                                                                                N
                                                                                                                Zt)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__275 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         21)) == (0b10100001000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           15
                                                                                                                           13)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           3
                                                                                                                           3)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__274 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__274 <b 2331) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__275 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 2331
                                                                                                                  let Rm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      5)
                                                                                                                  let msz :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      13
                                                                                                                      2)
                                                                                                                  let PNg :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      10
                                                                                                                      3)
                                                                                                                  let Rn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      5
                                                                                                                      5)
                                                                                                                  let T :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      4
                                                                                                                      1)
                                                                                                                  let N :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      3
                                                                                                                      1)
                                                                                                                  let Zt :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      3)
                                                                                                                  (decode_LD1W_MZx_P_BR_2x8
                                                                                                                    Rm
                                                                                                                    msz
                                                                                                                    PNg
                                                                                                                    Rn
                                                                                                                    T
                                                                                                                    N
                                                                                                                    Zt)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__277 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             21)) == (0b10100001000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               15
                                                                                                                               13)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               3
                                                                                                                               3)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__276 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__276 <b 2332) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__277 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 2332
                                                                                                                      let Rm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          5)
                                                                                                                      let msz :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          13
                                                                                                                          2)
                                                                                                                      let PNg :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          10
                                                                                                                          3)
                                                                                                                      let Rn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          5
                                                                                                                          5)
                                                                                                                      let T :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          4
                                                                                                                          1)
                                                                                                                      let N :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          3
                                                                                                                          1)
                                                                                                                      let Zt :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          3)
                                                                                                                      (decode_LD1D_MZx_P_BR_2x8
                                                                                                                        Rm
                                                                                                                        msz
                                                                                                                        PNg
                                                                                                                        Rn
                                                                                                                        T
                                                                                                                        N
                                                                                                                        Zt)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__279 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 21)) == (0b10100001000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   15
                                                                                                                                   13)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   3
                                                                                                                                   2)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__278 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__278 <b 2333) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__279 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 2333
                                                                                                                          let Rm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              5)
                                                                                                                          let msz :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              13
                                                                                                                              2)
                                                                                                                          let PNg :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              10
                                                                                                                              3)
                                                                                                                          let Rn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              5
                                                                                                                              5)
                                                                                                                          let T :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              4
                                                                                                                              1)
                                                                                                                          let N :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              3
                                                                                                                              1)
                                                                                                                          let Zt :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              2)
                                                                                                                          (decode_LD1B_MZx_P_BR_4x4
                                                                                                                            Rm
                                                                                                                            msz
                                                                                                                            PNg
                                                                                                                            Rn
                                                                                                                            T
                                                                                                                            N
                                                                                                                            Zt)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__281 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     21)) == (0b10100001000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       13)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       3
                                                                                                                                       2)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__280 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__280 <b 2334) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__281 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 2334
                                                                                                                              let Rm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  5)
                                                                                                                              let msz :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  13
                                                                                                                                  2)
                                                                                                                              let PNg :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  10
                                                                                                                                  3)
                                                                                                                              let Rn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  5
                                                                                                                                  5)
                                                                                                                              let T :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  4
                                                                                                                                  1)
                                                                                                                              let N :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  3
                                                                                                                                  1)
                                                                                                                              let Zt :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  2)
                                                                                                                              (decode_LD1H_MZx_P_BR_4x4
                                                                                                                                Rm
                                                                                                                                msz
                                                                                                                                PNg
                                                                                                                                Rn
                                                                                                                                T
                                                                                                                                N
                                                                                                                                Zt)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__283 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         21)) == (0b10100001000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           15
                                                                                                                                           13)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           3
                                                                                                                                           2)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__282 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__282 <b 2335) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__283 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 2335
                                                                                                                                  let Rm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      5)
                                                                                                                                  let msz :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      13
                                                                                                                                      2)
                                                                                                                                  let PNg :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      10
                                                                                                                                      3)
                                                                                                                                  let Rn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      5
                                                                                                                                      5)
                                                                                                                                  let T :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      4
                                                                                                                                      1)
                                                                                                                                  let N :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      3
                                                                                                                                      1)
                                                                                                                                  let Zt :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      2)
                                                                                                                                  (decode_LD1W_MZx_P_BR_4x4
                                                                                                                                    Rm
                                                                                                                                    msz
                                                                                                                                    PNg
                                                                                                                                    Rn
                                                                                                                                    T
                                                                                                                                    N
                                                                                                                                    Zt)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__285 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             21)) == (0b10100001000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               15
                                                                                                                                               13)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               3
                                                                                                                                               2)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__284 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__284 <b 2336) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__285 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 2336
                                                                                                                                      let Rm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          5)
                                                                                                                                      let msz :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          13
                                                                                                                                          2)
                                                                                                                                      let PNg :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          10
                                                                                                                                          3)
                                                                                                                                      let Rn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          5
                                                                                                                                          5)
                                                                                                                                      let T :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          4
                                                                                                                                          1)
                                                                                                                                      let N :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          3
                                                                                                                                          1)
                                                                                                                                      let Zt :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          2)
                                                                                                                                      (decode_LD1D_MZx_P_BR_4x4
                                                                                                                                        Rm
                                                                                                                                        msz
                                                                                                                                        PNg
                                                                                                                                        Rn
                                                                                                                                        T
                                                                                                                                        N
                                                                                                                                        Zt)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__287 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 21)) == (0b10100001000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   15
                                                                                                                                                   13)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   3
                                                                                                                                                   3)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__286 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__286 <b 2337) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__287 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 2337
                                                                                                                                          let Rm :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              5)
                                                                                                                                          let msz :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              13
                                                                                                                                              2)
                                                                                                                                          let PNg :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              10
                                                                                                                                              3)
                                                                                                                                          let Rn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              5)
                                                                                                                                          let T :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              4
                                                                                                                                              1)
                                                                                                                                          let N :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              3
                                                                                                                                              1)
                                                                                                                                          let Zt :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              3)
                                                                                                                                          (decode_LDNT1B_MZx_P_BR_2x8
                                                                                                                                            Rm
                                                                                                                                            msz
                                                                                                                                            PNg
                                                                                                                                            Rn
                                                                                                                                            T
                                                                                                                                            N
                                                                                                                                            Zt)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__289 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     21)) == (0b10100001000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       15
                                                                                                                                                       13)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       3
                                                                                                                                                       3)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__288 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__288 <b 2338) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__289 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 2338
                                                                                                                                              let Rm :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  5)
                                                                                                                                              let msz :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  13
                                                                                                                                                  2)
                                                                                                                                              let PNg :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  10
                                                                                                                                                  3)
                                                                                                                                              let Rn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  5
                                                                                                                                                  5)
                                                                                                                                              let T :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  4
                                                                                                                                                  1)
                                                                                                                                              let N :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  3
                                                                                                                                                  1)
                                                                                                                                              let Zt :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  3)
                                                                                                                                              (decode_LDNT1H_MZx_P_BR_2x8
                                                                                                                                                Rm
                                                                                                                                                msz
                                                                                                                                                PNg
                                                                                                                                                Rn
                                                                                                                                                T
                                                                                                                                                N
                                                                                                                                                Zt)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__291 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         21)) == (0b10100001000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           15
                                                                                                                                                           13)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           3
                                                                                                                                                           3)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__290 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__290 <b 2339) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__291 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 2339
                                                                                                                                                  let Rm :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      16
                                                                                                                                                      5)
                                                                                                                                                  let msz :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      13
                                                                                                                                                      2)
                                                                                                                                                  let PNg :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      10
                                                                                                                                                      3)
                                                                                                                                                  let Rn :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      5
                                                                                                                                                      5)
                                                                                                                                                  let T :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      4
                                                                                                                                                      1)
                                                                                                                                                  let N :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      3
                                                                                                                                                      1)
                                                                                                                                                  let Zt :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      3)
                                                                                                                                                  (decode_LDNT1W_MZx_P_BR_2x8
                                                                                                                                                    Rm
                                                                                                                                                    msz
                                                                                                                                                    PNg
                                                                                                                                                    Rn
                                                                                                                                                    T
                                                                                                                                                    N
                                                                                                                                                    Zt)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__293 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             21)) == (0b10100001000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               15
                                                                                                                                                               13)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               3
                                                                                                                                                               3)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__292 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__292 <b 2340) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__293 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 2340
                                                                                                                                                      let Rm :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          16
                                                                                                                                                          5)
                                                                                                                                                      let msz :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          13
                                                                                                                                                          2)
                                                                                                                                                      let PNg :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          10
                                                                                                                                                          3)
                                                                                                                                                      let Rn :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          5
                                                                                                                                                          5)
                                                                                                                                                      let T :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          4
                                                                                                                                                          1)
                                                                                                                                                      let N :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          3
                                                                                                                                                          1)
                                                                                                                                                      let Zt :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          3)
                                                                                                                                                      (decode_LDNT1D_MZx_P_BR_2x8
                                                                                                                                                        Rm
                                                                                                                                                        msz
                                                                                                                                                        PNg
                                                                                                                                                        Rn
                                                                                                                                                        T
                                                                                                                                                        N
                                                                                                                                                        Zt)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__295 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 21)) == (0b10100001000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   15
                                                                                                                                                                   13)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   3
                                                                                                                                                                   2)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__294 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__294 <b 2341) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__295 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 2341
                                                                                                                                                          let Rm :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              16
                                                                                                                                                              5)
                                                                                                                                                          let msz :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              13
                                                                                                                                                              2)
                                                                                                                                                          let PNg :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              10
                                                                                                                                                              3)
                                                                                                                                                          let Rn :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              5
                                                                                                                                                              5)
                                                                                                                                                          let T :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              4
                                                                                                                                                              1)
                                                                                                                                                          let N :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              3
                                                                                                                                                              1)
                                                                                                                                                          let Zt :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              0
                                                                                                                                                              2)
                                                                                                                                                          (decode_LDNT1B_MZx_P_BR_4x4
                                                                                                                                                            Rm
                                                                                                                                                            msz
                                                                                                                                                            PNg
                                                                                                                                                            Rn
                                                                                                                                                            T
                                                                                                                                                            N
                                                                                                                                                            Zt)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__297 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     31
                                                                                                                                                                     21)) == (0b10100001000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       15
                                                                                                                                                                       13)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       3
                                                                                                                                                                       2)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__296 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__296 <b 2342) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__297 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 2342
                                                                                                                                                              let Rm :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  16
                                                                                                                                                                  5)
                                                                                                                                                              let msz :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  13
                                                                                                                                                                  2)
                                                                                                                                                              let PNg :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  10
                                                                                                                                                                  3)
                                                                                                                                                              let Rn :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  5
                                                                                                                                                                  5)
                                                                                                                                                              let T :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  4
                                                                                                                                                                  1)
                                                                                                                                                              let N :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  3
                                                                                                                                                                  1)
                                                                                                                                                              let Zt :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  0
                                                                                                                                                                  2)
                                                                                                                                                              (decode_LDNT1H_MZx_P_BR_4x4
                                                                                                                                                                Rm
                                                                                                                                                                msz
                                                                                                                                                                PNg
                                                                                                                                                                Rn
                                                                                                                                                                T
                                                                                                                                                                N
                                                                                                                                                                Zt)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (pure true)))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
