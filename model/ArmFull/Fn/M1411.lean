import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1342
import ArmFull.Fn.M1343
import ArmFull.Fn.M1344

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
def __DecodeA64_SME__seg4 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__299 ← (( do
    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b10100001000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
               __opcode 15 13)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               __opcode 3 2)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
    then
      (do
        let w__298 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__298 <b 2343) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__299 : Bool)
  then
    (do
      writeReg SEE 2343
      let Rm := (BitVec.slice __opcode 16 5)
      let msz := (BitVec.slice __opcode 13 2)
      let PNg := (BitVec.slice __opcode 10 3)
      let Rn := (BitVec.slice __opcode 5 5)
      let T := (BitVec.slice __opcode 4 1)
      let N := (BitVec.slice __opcode 3 1)
      let Zt := (BitVec.slice __opcode 0 2)
      (decode_LDNT1W_MZx_P_BR_4x4 Rm msz PNg Rn T N Zt)
      (pure false))
  else
    (do
      let w__301 ← (( do
        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b10100001000#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                   __opcode 15 13)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                   __opcode 3 2)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
        then
          (do
            let w__300 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__300 <b 2344) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__301 : Bool)
      then
        (do
          writeReg SEE 2344
          let Rm := (BitVec.slice __opcode 16 5)
          let msz := (BitVec.slice __opcode 13 2)
          let PNg := (BitVec.slice __opcode 10 3)
          let Rn := (BitVec.slice __opcode 5 5)
          let T := (BitVec.slice __opcode 4 1)
          let N := (BitVec.slice __opcode 3 1)
          let Zt := (BitVec.slice __opcode 0 2)
          (decode_LDNT1D_MZx_P_BR_4x4 Rm msz PNg Rn T N Zt)
          (pure false))
      else
        (do
          let w__303 ← (( do
            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b10100001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                       __opcode 15 13)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 3 3)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
            then
              (do
                let w__302 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__302 <b 2345) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__303 : Bool)
          then
            (do
              writeReg SEE 2345
              let Rm := (BitVec.slice __opcode 16 5)
              let msz := (BitVec.slice __opcode 13 2)
              let PNg := (BitVec.slice __opcode 10 3)
              let Rn := (BitVec.slice __opcode 5 5)
              let T := (BitVec.slice __opcode 4 1)
              let N := (BitVec.slice __opcode 3 1)
              let Zt := (BitVec.slice __opcode 0 3)
              (decode_ST1B_MZx_P_BR_2x8 Rm msz PNg Rn T N Zt)
              (pure false))
          else
            (do
              let w__305 ← (( do
                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b10100001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                           __opcode 15 13)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 3 3)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                then
                  (do
                    let w__304 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__304 <b 2346) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__305 : Bool)
              then
                (do
                  writeReg SEE 2346
                  let Rm := (BitVec.slice __opcode 16 5)
                  let msz := (BitVec.slice __opcode 13 2)
                  let PNg := (BitVec.slice __opcode 10 3)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let T := (BitVec.slice __opcode 4 1)
                  let N := (BitVec.slice __opcode 3 1)
                  let Zt := (BitVec.slice __opcode 0 3)
                  (decode_ST1H_MZx_P_BR_2x8 Rm msz PNg Rn T N Zt)
                  (pure false))
              else
                (do
                  let w__307 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b10100001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                               __opcode 15 13)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 3 3)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                    then
                      (do
                        let w__306 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__306 <b 2347) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__307 : Bool)
                  then
                    (do
                      writeReg SEE 2347
                      let Rm := (BitVec.slice __opcode 16 5)
                      let msz := (BitVec.slice __opcode 13 2)
                      let PNg := (BitVec.slice __opcode 10 3)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let T := (BitVec.slice __opcode 4 1)
                      let N := (BitVec.slice __opcode 3 1)
                      let Zt := (BitVec.slice __opcode 0 3)
                      (decode_ST1W_MZx_P_BR_2x8 Rm msz PNg Rn T N Zt)
                      (pure false))
                  else
                    (do
                      let w__309 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31
                                 21)) == (0b10100001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                   __opcode 15 13)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 3 3)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                        then
                          (do
                            let w__308 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__308 <b 2348) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__309 : Bool)
                      then
                        (do
                          writeReg SEE 2348
                          let Rm := (BitVec.slice __opcode 16 5)
                          let msz := (BitVec.slice __opcode 13 2)
                          let PNg := (BitVec.slice __opcode 10 3)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let T := (BitVec.slice __opcode 4 1)
                          let N := (BitVec.slice __opcode 3 1)
                          let Zt := (BitVec.slice __opcode 0 3)
                          (decode_ST1D_MZx_P_BR_2x8 Rm msz PNg Rn T N Zt)
                          (pure false))
                      else
                        (do
                          let w__311 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode
                                     31 21)) == (0b10100001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                       __opcode 15 13)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                       __opcode 3 2)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                            then
                              (do
                                let w__310 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__310 <b 2349) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__311 : Bool)
                          then
                            (do
                              writeReg SEE 2349
                              let Rm := (BitVec.slice __opcode 16 5)
                              let msz := (BitVec.slice __opcode 13 2)
                              let PNg := (BitVec.slice __opcode 10 3)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let T := (BitVec.slice __opcode 4 1)
                              let N := (BitVec.slice __opcode 3 1)
                              let Zt := (BitVec.slice __opcode 0 2)
                              (decode_ST1B_MZx_P_BR_4x4 Rm msz PNg Rn T N Zt)
                              (pure false))
                          else
                            (do
                              let w__313 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                         __opcode 31 21)) == (0b10100001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                           __opcode 15 13)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                           __opcode 3 2)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__312 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__312 <b 2350) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__313 : Bool)
                              then
                                (do
                                  writeReg SEE 2350
                                  let Rm := (BitVec.slice __opcode 16 5)
                                  let msz := (BitVec.slice __opcode 13 2)
                                  let PNg := (BitVec.slice __opcode 10 3)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let T := (BitVec.slice __opcode 4 1)
                                  let N := (BitVec.slice __opcode 3 1)
                                  let Zt := (BitVec.slice __opcode 0 2)
                                  (decode_ST1H_MZx_P_BR_4x4 Rm msz PNg Rn T N Zt)
                                  (pure false))
                              else
                                (do
                                  let w__315 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                             __opcode 31 21)) == (0b10100001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                               __opcode 15 13)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                               __opcode 3 2)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__314 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__314 <b 2351) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__315 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2351
                                      let Rm := (BitVec.slice __opcode 16 5)
                                      let msz := (BitVec.slice __opcode 13 2)
                                      let PNg := (BitVec.slice __opcode 10 3)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let T := (BitVec.slice __opcode 4 1)
                                      let N := (BitVec.slice __opcode 3 1)
                                      let Zt := (BitVec.slice __opcode 0 2)
                                      (decode_ST1W_MZx_P_BR_4x4 Rm msz PNg Rn T N Zt)
                                      (pure false))
                                  else
                                    (do
                                      let w__317 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                 __opcode 31 21)) == (0b10100001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                   __opcode 15 13)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                   __opcode 3 2)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__316 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__316 <b 2352) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__317 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2352
                                          let Rm := (BitVec.slice __opcode 16 5)
                                          let msz := (BitVec.slice __opcode 13 2)
                                          let PNg := (BitVec.slice __opcode 10 3)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let T := (BitVec.slice __opcode 4 1)
                                          let N := (BitVec.slice __opcode 3 1)
                                          let Zt := (BitVec.slice __opcode 0 2)
                                          (decode_ST1D_MZx_P_BR_4x4 Rm msz PNg Rn T N Zt)
                                          (pure false))
                                      else
                                        (do
                                          let w__319 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                     __opcode 31 21)) == (0b10100001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                       __opcode 15 13)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 3 3)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__318 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__318 <b 2353) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__319 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2353
                                              let Rm := (BitVec.slice __opcode 16 5)
                                              let msz := (BitVec.slice __opcode 13 2)
                                              let PNg := (BitVec.slice __opcode 10 3)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let T := (BitVec.slice __opcode 4 1)
                                              let N := (BitVec.slice __opcode 3 1)
                                              let Zt := (BitVec.slice __opcode 0 3)
                                              (decode_STNT1B_MZx_P_BR_2x8 Rm msz PNg Rn T N Zt)
                                              (pure false))
                                          else
                                            (do
                                              let w__321 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                         __opcode 31 21)) == (0b10100001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                           __opcode 15 13)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 3 3)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__320 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__320 <b 2354) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__321 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2354
                                                  let Rm := (BitVec.slice __opcode 16 5)
                                                  let msz := (BitVec.slice __opcode 13 2)
                                                  let PNg := (BitVec.slice __opcode 10 3)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let T := (BitVec.slice __opcode 4 1)
                                                  let N := (BitVec.slice __opcode 3 1)
                                                  let Zt := (BitVec.slice __opcode 0 3)
                                                  (decode_STNT1H_MZx_P_BR_2x8 Rm msz PNg Rn T N Zt)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__323 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                             __opcode 31 21)) == (0b10100001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                               __opcode 15 13)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 3 3)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__322 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__322 <b 2355) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__323 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2355
                                                      let Rm := (BitVec.slice __opcode 16 5)
                                                      let msz := (BitVec.slice __opcode 13 2)
                                                      let PNg := (BitVec.slice __opcode 10 3)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let T := (BitVec.slice __opcode 4 1)
                                                      let N := (BitVec.slice __opcode 3 1)
                                                      let Zt := (BitVec.slice __opcode 0 3)
                                                      (decode_STNT1W_MZx_P_BR_2x8 Rm msz PNg Rn T N
                                                        Zt)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__325 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                 __opcode 31 21)) == (0b10100001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                   __opcode 15 13)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 3 3)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__324 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__324 <b 2356) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__325 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2356
                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                          let msz := (BitVec.slice __opcode 13 2)
                                                          let PNg := (BitVec.slice __opcode 10 3)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let T := (BitVec.slice __opcode 4 1)
                                                          let N := (BitVec.slice __opcode 3 1)
                                                          let Zt := (BitVec.slice __opcode 0 3)
                                                          (decode_STNT1D_MZx_P_BR_2x8 Rm msz PNg Rn
                                                            T N Zt)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__327 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                     __opcode 31 21)) == (0b10100001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                       __opcode 15 13)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                       __opcode 3 2)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__326 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__326 <b 2357) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__327 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2357
                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                              let msz :=
                                                                (BitVec.slice __opcode 13 2)
                                                              let PNg :=
                                                                (BitVec.slice __opcode 10 3)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let T := (BitVec.slice __opcode 4 1)
                                                              let N := (BitVec.slice __opcode 3 1)
                                                              let Zt := (BitVec.slice __opcode 0 2)
                                                              (decode_STNT1B_MZx_P_BR_4x4 Rm msz PNg
                                                                Rn T N Zt)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__329 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                         __opcode 31 21)) == (0b10100001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                           __opcode 15 13)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                           __opcode 3 2)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__328 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__328 <b 2358) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__329 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2358
                                                                  let Rm :=
                                                                    (BitVec.slice __opcode 16 5)
                                                                  let msz :=
                                                                    (BitVec.slice __opcode 13 2)
                                                                  let PNg :=
                                                                    (BitVec.slice __opcode 10 3)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let T :=
                                                                    (BitVec.slice __opcode 4 1)
                                                                  let N :=
                                                                    (BitVec.slice __opcode 3 1)
                                                                  let Zt :=
                                                                    (BitVec.slice __opcode 0 2)
                                                                  (decode_STNT1H_MZx_P_BR_4x4 Rm msz
                                                                    PNg Rn T N Zt)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__331 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                             __opcode 31 21)) == (0b10100001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                               __opcode 15 13)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                               __opcode 3 2)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__330 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__330 <b 2359) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__331 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2359
                                                                      let Rm :=
                                                                        (BitVec.slice __opcode 16 5)
                                                                      let msz :=
                                                                        (BitVec.slice __opcode 13 2)
                                                                      let PNg :=
                                                                        (BitVec.slice __opcode 10 3)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let T :=
                                                                        (BitVec.slice __opcode 4 1)
                                                                      let N :=
                                                                        (BitVec.slice __opcode 3 1)
                                                                      let Zt :=
                                                                        (BitVec.slice __opcode 0 2)
                                                                      (decode_STNT1W_MZx_P_BR_4x4 Rm
                                                                        msz PNg Rn T N Zt)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__333 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 21)) == (0b10100001001#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                   __opcode 15 13)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                   __opcode 3 2)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__332 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__332 <b 2360) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__333 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2360
                                                                          let Rm :=
                                                                            (BitVec.slice __opcode
                                                                              16 5)
                                                                          let msz :=
                                                                            (BitVec.slice __opcode
                                                                              13 2)
                                                                          let PNg :=
                                                                            (BitVec.slice __opcode
                                                                              10 3)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let T :=
                                                                            (BitVec.slice __opcode 4
                                                                              1)
                                                                          let N :=
                                                                            (BitVec.slice __opcode 3
                                                                              1)
                                                                          let Zt :=
                                                                            (BitVec.slice __opcode 0
                                                                              2)
                                                                          (decode_STNT1D_MZx_P_BR_4x4
                                                                            Rm msz PNg Rn T N Zt)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__335 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 20)) == (0xA14#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                       __opcode 15
                                                                                       13)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 3 3)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__334 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__334 <b 2361) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__335 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2361
                                                                              let imm4 :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let msz :=
                                                                                (BitVec.slice
                                                                                  __opcode 13 2)
                                                                              let PNg :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 3)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let T :=
                                                                                (BitVec.slice
                                                                                  __opcode 4 1)
                                                                              let N :=
                                                                                (BitVec.slice
                                                                                  __opcode 3 1)
                                                                              let Zt :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 3)
                                                                              (decode_LD1B_MZx_P_BI_2x8
                                                                                imm4 msz PNg Rn T N
                                                                                Zt)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__337 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         20)) == (0xA14#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           15 13)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           3 3)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__336 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__336 <b 2362) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__337 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2362
                                                                                  let imm4 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let msz :=
                                                                                    (BitVec.slice
                                                                                      __opcode 13 2)
                                                                                  let PNg :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 3)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let T :=
                                                                                    (BitVec.slice
                                                                                      __opcode 4 1)
                                                                                  let N :=
                                                                                    (BitVec.slice
                                                                                      __opcode 3 1)
                                                                                  let Zt :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 3)
                                                                                  (decode_LD1H_MZx_P_BI_2x8
                                                                                    imm4 msz PNg Rn
                                                                                    T N Zt)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__339 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 20)) == (0xA14#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               15 13)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               3 3)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__338 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__338 <b 2363) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__339 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2363
                                                                                      let imm4 :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let msz :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          13 2)
                                                                                      let PNg :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 3)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let T :=
                                                                                        (BitVec.slice
                                                                                          __opcode 4
                                                                                          1)
                                                                                      let N :=
                                                                                        (BitVec.slice
                                                                                          __opcode 3
                                                                                          1)
                                                                                      let Zt :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          3)
                                                                                      (decode_LD1W_MZx_P_BI_2x8
                                                                                        imm4 msz PNg
                                                                                        Rn T N Zt)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__341 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 20)) == (0xA14#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   15
                                                                                                   13)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   3
                                                                                                   3)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__340 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__340 <b 2364) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__341 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2364
                                                                                          let imm4 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let msz :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              13 2)
                                                                                          let PNg :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 3)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let T :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              4 1)
                                                                                          let N :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              3 1)
                                                                                          let Zt :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 3)
                                                                                          (decode_LD1D_MZx_P_BI_2x8
                                                                                            imm4 msz
                                                                                            PNg Rn T
                                                                                            N Zt)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__343 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     20)) == (0xA14#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       15
                                                                                                       13)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       3
                                                                                                       3)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__342 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__342 <b 2365) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__343 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2365
                                                                                              let imm4 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  4)
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
                                                                                              (decode_LDNT1B_MZx_P_BI_2x8
                                                                                                imm4
                                                                                                msz
                                                                                                PNg
                                                                                                Rn T
                                                                                                N Zt)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__345 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         20)) == (0xA14#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           15
                                                                                                           13)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           3
                                                                                                           3)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__344 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__344 <b 2366) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__345 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2366
                                                                                                  let imm4 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      4)
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
                                                                                                  (decode_LDNT1H_MZx_P_BI_2x8
                                                                                                    imm4
                                                                                                    msz
                                                                                                    PNg
                                                                                                    Rn
                                                                                                    T
                                                                                                    N
                                                                                                    Zt)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__347 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             20)) == (0xA14#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               13)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               3
                                                                                                               3)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__346 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__346 <b 2367) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__347 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 2367
                                                                                                      let imm4 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          4)
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
                                                                                                      (decode_LDNT1W_MZx_P_BI_2x8
                                                                                                        imm4
                                                                                                        msz
                                                                                                        PNg
                                                                                                        Rn
                                                                                                        T
                                                                                                        N
                                                                                                        Zt)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__349 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 20)) == (0xA14#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   15
                                                                                                                   13)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   3
                                                                                                                   3)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__348 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__348 <b 2368) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__349 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 2368
                                                                                                          let imm4 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              4)
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
                                                                                                          (decode_LDNT1D_MZx_P_BI_2x8
                                                                                                            imm4
                                                                                                            msz
                                                                                                            PNg
                                                                                                            Rn
                                                                                                            T
                                                                                                            N
                                                                                                            Zt)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__351 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     20)) == (0xA14#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       15
                                                                                                                       13)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       3
                                                                                                                       2)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__350 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__350 <b 2369) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__351 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 2369
                                                                                                              let imm4 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  4)
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
                                                                                                              (decode_LD1B_MZx_P_BI_4x4
                                                                                                                imm4
                                                                                                                msz
                                                                                                                PNg
                                                                                                                Rn
                                                                                                                T
                                                                                                                N
                                                                                                                Zt)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__353 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         20)) == (0xA14#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           15
                                                                                                                           13)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           3
                                                                                                                           2)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__352 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__352 <b 2370) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__353 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 2370
                                                                                                                  let imm4 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      4)
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
                                                                                                                  (decode_LD1H_MZx_P_BI_4x4
                                                                                                                    imm4
                                                                                                                    msz
                                                                                                                    PNg
                                                                                                                    Rn
                                                                                                                    T
                                                                                                                    N
                                                                                                                    Zt)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__355 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             20)) == (0xA14#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               15
                                                                                                                               13)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               3
                                                                                                                               2)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__354 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__354 <b 2371) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__355 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 2371
                                                                                                                      let imm4 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          4)
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
                                                                                                                      (decode_LD1W_MZx_P_BI_4x4
                                                                                                                        imm4
                                                                                                                        msz
                                                                                                                        PNg
                                                                                                                        Rn
                                                                                                                        T
                                                                                                                        N
                                                                                                                        Zt)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__357 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 20)) == (0xA14#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   15
                                                                                                                                   13)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   3
                                                                                                                                   2)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__356 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__356 <b 2372) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__357 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 2372
                                                                                                                          let imm4 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              4)
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
                                                                                                                          (decode_LD1D_MZx_P_BI_4x4
                                                                                                                            imm4
                                                                                                                            msz
                                                                                                                            PNg
                                                                                                                            Rn
                                                                                                                            T
                                                                                                                            N
                                                                                                                            Zt)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__359 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     20)) == (0xA14#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       13)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       3
                                                                                                                                       2)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__358 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__358 <b 2373) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__359 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 2373
                                                                                                                              let imm4 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  4)
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
                                                                                                                              (decode_LDNT1B_MZx_P_BI_4x4
                                                                                                                                imm4
                                                                                                                                msz
                                                                                                                                PNg
                                                                                                                                Rn
                                                                                                                                T
                                                                                                                                N
                                                                                                                                Zt)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__361 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         20)) == (0xA14#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           15
                                                                                                                                           13)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           3
                                                                                                                                           2)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__360 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__360 <b 2374) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__361 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 2374
                                                                                                                                  let imm4 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      4)
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
                                                                                                                                  (decode_LDNT1H_MZx_P_BI_4x4
                                                                                                                                    imm4
                                                                                                                                    msz
                                                                                                                                    PNg
                                                                                                                                    Rn
                                                                                                                                    T
                                                                                                                                    N
                                                                                                                                    Zt)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__363 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             20)) == (0xA14#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               15
                                                                                                                                               13)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               3
                                                                                                                                               2)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__362 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__362 <b 2375) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__363 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 2375
                                                                                                                                      let imm4 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          4)
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
                                                                                                                                      (decode_LDNT1W_MZx_P_BI_4x4
                                                                                                                                        imm4
                                                                                                                                        msz
                                                                                                                                        PNg
                                                                                                                                        Rn
                                                                                                                                        T
                                                                                                                                        N
                                                                                                                                        Zt)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__365 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 20)) == (0xA14#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   15
                                                                                                                                                   13)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   3
                                                                                                                                                   2)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__364 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__364 <b 2376) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__365 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 2376
                                                                                                                                          let imm4 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              4)
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
                                                                                                                                          (decode_LDNT1D_MZx_P_BI_4x4
                                                                                                                                            imm4
                                                                                                                                            msz
                                                                                                                                            PNg
                                                                                                                                            Rn
                                                                                                                                            T
                                                                                                                                            N
                                                                                                                                            Zt)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (pure true))))))))))))))))))))))))))))))))))


end ArmFull.Functions
