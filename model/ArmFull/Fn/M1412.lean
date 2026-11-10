import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1161
import ArmFull.Fn.M1162
import ArmFull.Fn.M1163
import ArmFull.Fn.M1344
import ArmFull.Fn.M1345

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
def __DecodeA64_SME__seg5 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__367 ← (( do
    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xA16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
               __opcode 15 13)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 3 3)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
    then
      (do
        let w__366 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__366 <b 2377) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__367 : Bool)
  then
    (do
      writeReg SEE 2377
      let imm4 := (BitVec.slice __opcode 16 4)
      let msz := (BitVec.slice __opcode 13 2)
      let PNg := (BitVec.slice __opcode 10 3)
      let Rn := (BitVec.slice __opcode 5 5)
      let T := (BitVec.slice __opcode 4 1)
      let N := (BitVec.slice __opcode 3 1)
      let Zt := (BitVec.slice __opcode 0 3)
      (decode_ST1B_MZx_P_BI_2x8 imm4 msz PNg Rn T N Zt)
      (pure false))
  else
    (do
      let w__369 ← (( do
        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xA16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                   __opcode 15 13)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 3 3)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
        then
          (do
            let w__368 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__368 <b 2378) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__369 : Bool)
      then
        (do
          writeReg SEE 2378
          let imm4 := (BitVec.slice __opcode 16 4)
          let msz := (BitVec.slice __opcode 13 2)
          let PNg := (BitVec.slice __opcode 10 3)
          let Rn := (BitVec.slice __opcode 5 5)
          let T := (BitVec.slice __opcode 4 1)
          let N := (BitVec.slice __opcode 3 1)
          let Zt := (BitVec.slice __opcode 0 3)
          (decode_ST1H_MZx_P_BI_2x8 imm4 msz PNg Rn T N Zt)
          (pure false))
      else
        (do
          let w__371 ← (( do
            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xA16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                       __opcode 15 13)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 3 3)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
            then
              (do
                let w__370 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__370 <b 2379) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__371 : Bool)
          then
            (do
              writeReg SEE 2379
              let imm4 := (BitVec.slice __opcode 16 4)
              let msz := (BitVec.slice __opcode 13 2)
              let PNg := (BitVec.slice __opcode 10 3)
              let Rn := (BitVec.slice __opcode 5 5)
              let T := (BitVec.slice __opcode 4 1)
              let N := (BitVec.slice __opcode 3 1)
              let Zt := (BitVec.slice __opcode 0 3)
              (decode_ST1W_MZx_P_BI_2x8 imm4 msz PNg Rn T N Zt)
              (pure false))
          else
            (do
              let w__373 ← (( do
                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xA16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                           __opcode 15 13)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 3 3)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                then
                  (do
                    let w__372 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__372 <b 2380) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__373 : Bool)
              then
                (do
                  writeReg SEE 2380
                  let imm4 := (BitVec.slice __opcode 16 4)
                  let msz := (BitVec.slice __opcode 13 2)
                  let PNg := (BitVec.slice __opcode 10 3)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let T := (BitVec.slice __opcode 4 1)
                  let N := (BitVec.slice __opcode 3 1)
                  let Zt := (BitVec.slice __opcode 0 3)
                  (decode_ST1D_MZx_P_BI_2x8 imm4 msz PNg Rn T N Zt)
                  (pure false))
              else
                (do
                  let w__375 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xA16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                               __opcode 15 13)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                               __opcode 3 2)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                    then
                      (do
                        let w__374 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__374 <b 2381) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__375 : Bool)
                  then
                    (do
                      writeReg SEE 2381
                      let imm4 := (BitVec.slice __opcode 16 4)
                      let msz := (BitVec.slice __opcode 13 2)
                      let PNg := (BitVec.slice __opcode 10 3)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let T := (BitVec.slice __opcode 4 1)
                      let N := (BitVec.slice __opcode 3 1)
                      let Zt := (BitVec.slice __opcode 0 2)
                      (decode_ST1B_MZx_P_BI_4x4 imm4 msz PNg Rn T N Zt)
                      (pure false))
                  else
                    (do
                      let w__377 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31
                                 20)) == (0xA16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                   __opcode 15 13)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                   __opcode 3 2)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                        then
                          (do
                            let w__376 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__376 <b 2382) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__377 : Bool)
                      then
                        (do
                          writeReg SEE 2382
                          let imm4 := (BitVec.slice __opcode 16 4)
                          let msz := (BitVec.slice __opcode 13 2)
                          let PNg := (BitVec.slice __opcode 10 3)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let T := (BitVec.slice __opcode 4 1)
                          let N := (BitVec.slice __opcode 3 1)
                          let Zt := (BitVec.slice __opcode 0 2)
                          (decode_ST1H_MZx_P_BI_4x4 imm4 msz PNg Rn T N Zt)
                          (pure false))
                      else
                        (do
                          let w__379 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode
                                     31 20)) == (0xA16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                       __opcode 15 13)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                       __opcode 3 2)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                            then
                              (do
                                let w__378 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__378 <b 2383) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__379 : Bool)
                          then
                            (do
                              writeReg SEE 2383
                              let imm4 := (BitVec.slice __opcode 16 4)
                              let msz := (BitVec.slice __opcode 13 2)
                              let PNg := (BitVec.slice __opcode 10 3)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let T := (BitVec.slice __opcode 4 1)
                              let N := (BitVec.slice __opcode 3 1)
                              let Zt := (BitVec.slice __opcode 0 2)
                              (decode_ST1W_MZx_P_BI_4x4 imm4 msz PNg Rn T N Zt)
                              (pure false))
                          else
                            (do
                              let w__381 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                         __opcode 31 20)) == (0xA16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                           __opcode 15 13)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                           __opcode 3 2)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__380 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__380 <b 2384) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__381 : Bool)
                              then
                                (do
                                  writeReg SEE 2384
                                  let imm4 := (BitVec.slice __opcode 16 4)
                                  let msz := (BitVec.slice __opcode 13 2)
                                  let PNg := (BitVec.slice __opcode 10 3)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let T := (BitVec.slice __opcode 4 1)
                                  let N := (BitVec.slice __opcode 3 1)
                                  let Zt := (BitVec.slice __opcode 0 2)
                                  (decode_ST1D_MZx_P_BI_4x4 imm4 msz PNg Rn T N Zt)
                                  (pure false))
                              else
                                (do
                                  let w__383 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                             __opcode 31 20)) == (0xA16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                               __opcode 15 13)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 3 3)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__382 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__382 <b 2385) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__383 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2385
                                      let imm4 := (BitVec.slice __opcode 16 4)
                                      let msz := (BitVec.slice __opcode 13 2)
                                      let PNg := (BitVec.slice __opcode 10 3)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let T := (BitVec.slice __opcode 4 1)
                                      let N := (BitVec.slice __opcode 3 1)
                                      let Zt := (BitVec.slice __opcode 0 3)
                                      (decode_STNT1B_MZx_P_BI_2x8 imm4 msz PNg Rn T N Zt)
                                      (pure false))
                                  else
                                    (do
                                      let w__385 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                 __opcode 31 20)) == (0xA16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                   __opcode 15 13)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                   __opcode 3 3)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__384 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__384 <b 2386) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__385 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2386
                                          let imm4 := (BitVec.slice __opcode 16 4)
                                          let msz := (BitVec.slice __opcode 13 2)
                                          let PNg := (BitVec.slice __opcode 10 3)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let T := (BitVec.slice __opcode 4 1)
                                          let N := (BitVec.slice __opcode 3 1)
                                          let Zt := (BitVec.slice __opcode 0 3)
                                          (decode_STNT1H_MZx_P_BI_2x8 imm4 msz PNg Rn T N Zt)
                                          (pure false))
                                      else
                                        (do
                                          let w__387 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                     __opcode 31 20)) == (0xA16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                       __opcode 15 13)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 3 3)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__386 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__386 <b 2387) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__387 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2387
                                              let imm4 := (BitVec.slice __opcode 16 4)
                                              let msz := (BitVec.slice __opcode 13 2)
                                              let PNg := (BitVec.slice __opcode 10 3)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let T := (BitVec.slice __opcode 4 1)
                                              let N := (BitVec.slice __opcode 3 1)
                                              let Zt := (BitVec.slice __opcode 0 3)
                                              (decode_STNT1W_MZx_P_BI_2x8 imm4 msz PNg Rn T N Zt)
                                              (pure false))
                                          else
                                            (do
                                              let w__389 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                         __opcode 31 20)) == (0xA16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                           __opcode 15 13)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 3 3)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__388 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__388 <b 2388) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__389 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2388
                                                  let imm4 := (BitVec.slice __opcode 16 4)
                                                  let msz := (BitVec.slice __opcode 13 2)
                                                  let PNg := (BitVec.slice __opcode 10 3)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let T := (BitVec.slice __opcode 4 1)
                                                  let N := (BitVec.slice __opcode 3 1)
                                                  let Zt := (BitVec.slice __opcode 0 3)
                                                  (decode_STNT1D_MZx_P_BI_2x8 imm4 msz PNg Rn T N Zt)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__391 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                             __opcode 31 20)) == (0xA16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                               __opcode 15 13)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                               __opcode 3 2)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__390 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__390 <b 2389) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__391 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2389
                                                      let imm4 := (BitVec.slice __opcode 16 4)
                                                      let msz := (BitVec.slice __opcode 13 2)
                                                      let PNg := (BitVec.slice __opcode 10 3)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let T := (BitVec.slice __opcode 4 1)
                                                      let N := (BitVec.slice __opcode 3 1)
                                                      let Zt := (BitVec.slice __opcode 0 2)
                                                      (decode_STNT1B_MZx_P_BI_4x4 imm4 msz PNg Rn T
                                                        N Zt)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__393 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                 __opcode 31 20)) == (0xA16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                   __opcode 15 13)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                   __opcode 3 2)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__392 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__392 <b 2390) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__393 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2390
                                                          let imm4 := (BitVec.slice __opcode 16 4)
                                                          let msz := (BitVec.slice __opcode 13 2)
                                                          let PNg := (BitVec.slice __opcode 10 3)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let T := (BitVec.slice __opcode 4 1)
                                                          let N := (BitVec.slice __opcode 3 1)
                                                          let Zt := (BitVec.slice __opcode 0 2)
                                                          (decode_STNT1H_MZx_P_BI_4x4 imm4 msz PNg
                                                            Rn T N Zt)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__395 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                     __opcode 31 20)) == (0xA16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                       __opcode 15 13)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                       __opcode 3 2)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__394 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__394 <b 2391) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__395 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2391
                                                              let imm4 :=
                                                                (BitVec.slice __opcode 16 4)
                                                              let msz :=
                                                                (BitVec.slice __opcode 13 2)
                                                              let PNg :=
                                                                (BitVec.slice __opcode 10 3)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let T := (BitVec.slice __opcode 4 1)
                                                              let N := (BitVec.slice __opcode 3 1)
                                                              let Zt := (BitVec.slice __opcode 0 2)
                                                              (decode_STNT1W_MZx_P_BI_4x4 imm4 msz
                                                                PNg Rn T N Zt)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__397 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                         __opcode 31 20)) == (0xA16#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                           __opcode 15 13)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                           __opcode 3 2)) == (0b10#2 : (BitVec 2))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__396 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__396 <b 2392) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__397 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2392
                                                                  let imm4 :=
                                                                    (BitVec.slice __opcode 16 4)
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
                                                                  (decode_STNT1D_MZx_P_BI_4x4 imm4
                                                                    msz PNg Rn T N Zt)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__399 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                             __opcode 31 23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                               __opcode 21 15)) == (0b1000000#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                 __opcode 12 10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                 __opcode 5 3)) == (0b000#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__398 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__398 <b 2393) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__399 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2393
                                                                      let sz :=
                                                                        (BitVec.slice __opcode 22 1)
                                                                      let Rv :=
                                                                        (BitVec.slice __opcode 13 2)
                                                                      let Zm :=
                                                                        (BitVec.slice __opcode 6 4)
                                                                      let S :=
                                                                        (BitVec.slice __opcode 3 1)
                                                                      let off3 :=
                                                                        (BitVec.slice __opcode 0 3)
                                                                      (decode_FADD_ZA_ZW_2x2 sz Rv
                                                                        Zm S off3)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__401 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 15)) == (0b1000000#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                     __opcode 12 10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                     __opcode 5 3)) == (0b001#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__400 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__400 <b 2394) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__401 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2394
                                                                          let sz :=
                                                                            (BitVec.slice __opcode
                                                                              22 1)
                                                                          let Rv :=
                                                                            (BitVec.slice __opcode
                                                                              13 2)
                                                                          let Zm :=
                                                                            (BitVec.slice __opcode 6
                                                                              4)
                                                                          let S :=
                                                                            (BitVec.slice __opcode 3
                                                                              1)
                                                                          let off3 :=
                                                                            (BitVec.slice __opcode 0
                                                                              3)
                                                                          (decode_FSUB_ZA_ZW_2x2 sz
                                                                            Rv Zm S off3)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__403 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       15)) == (0b1000010#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                         __opcode 12
                                                                                         10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                         __opcode 6
                                                                                         3)) == (0x0#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__402 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__402 <b 2395) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__403 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2395
                                                                              let sz :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              let Rv :=
                                                                                (BitVec.slice
                                                                                  __opcode 13 2)
                                                                              let Zm :=
                                                                                (BitVec.slice
                                                                                  __opcode 7 3)
                                                                              let S :=
                                                                                (BitVec.slice
                                                                                  __opcode 3 1)
                                                                              let off3 :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 3)
                                                                              (decode_FADD_ZA_ZW_4x4
                                                                                sz Rv Zm S off3)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__405 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 15)) == (0b1000010#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             12 10)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             6 3)) == (0x1#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__404 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__404 <b 2396) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__405 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2396
                                                                                  let sz :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  let Rv :=
                                                                                    (BitVec.slice
                                                                                      __opcode 13 2)
                                                                                  let Zm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 7 3)
                                                                                  let S :=
                                                                                    (BitVec.slice
                                                                                      __opcode 3 1)
                                                                                  let off3 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 3)
                                                                                  (decode_FSUB_ZA_ZW_4x4
                                                                                    sz Rv Zm S off3)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__407 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 16
                                                                                                 15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   12
                                                                                                   10)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   5
                                                                                                   3)) == (0b000#3 : (BitVec 3))))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__406 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__406 <b 2397) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__407 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2397
                                                                                      let sz :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 1)
                                                                                      let Zm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          17 4)
                                                                                      let Rv :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          13 2)
                                                                                      let Zn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 6
                                                                                          4)
                                                                                      let S :=
                                                                                        (BitVec.slice
                                                                                          __opcode 3
                                                                                          1)
                                                                                      let off3 :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          3)
                                                                                      (decode_FMLA_ZA_ZZW_2x2
                                                                                        sz Zm Rv Zn
                                                                                        S off3)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__409 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     16
                                                                                                     15)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       12
                                                                                                       10)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       5
                                                                                                       3)) == (0b001#3 : (BitVec 3))))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__408 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__408 <b 2398) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__409 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2398
                                                                                          let sz :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let Zm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              17 4)
                                                                                          let Rv :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              13 2)
                                                                                          let Zn :=
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
                                                                                          (decode_FMLS_ZA_ZZW_2x2
                                                                                            sz Zm Rv
                                                                                            Zn S
                                                                                            off3)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__411 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         15
                                                                                                         15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           12
                                                                                                           10)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           4
                                                                                                           3)) == (0b00#2 : (BitVec 2))))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__410 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__410 <b 2399) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__411 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2399
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
                                                                                              (decode_FMLA_ZA_ZZV_2x1
                                                                                                sz
                                                                                                Zm
                                                                                                Rv
                                                                                                Zn S
                                                                                                off3)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__413 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           21
                                                                                                           20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             15
                                                                                                             15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               12
                                                                                                               10)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               4
                                                                                                               3)) == (0b01#2 : (BitVec 2))))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__412 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__412 <b 2400) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__413 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2400
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
                                                                                                  (decode_FMLS_ZA_ZZV_2x1
                                                                                                    sz
                                                                                                    Zm
                                                                                                    Rv
                                                                                                    Zn
                                                                                                    S
                                                                                                    off3)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__415 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 17
                                                                                                                 15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   12
                                                                                                                   10)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   6
                                                                                                                   3)) == (0x0#4 : (BitVec 4))))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__414 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__414 <b 2401) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__415 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 2401
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
                                                                                                          3
                                                                                                          1)
                                                                                                      let off3 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          3)
                                                                                                      (decode_FMLA_ZA_ZZW_4x4
                                                                                                        sz
                                                                                                        Zm
                                                                                                        Rv
                                                                                                        Zn
                                                                                                        S
                                                                                                        off3)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__417 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 23)) == (0b110000011#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   21
                                                                                                                   21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     17
                                                                                                                     15)) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       12
                                                                                                                       10)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       6
                                                                                                                       3)) == (0x1#4 : (BitVec 4))))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__416 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__416 <b 2402) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__417 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 2402
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
                                                                                                              3
                                                                                                              1)
                                                                                                          let off3 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              3)
                                                                                                          (decode_FMLS_ZA_ZZW_4x4
                                                                                                            sz
                                                                                                            Zm
                                                                                                            Rv
                                                                                                            Zn
                                                                                                            S
                                                                                                            off3)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__419 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       21
                                                                                                                       20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         15
                                                                                                                         15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           12
                                                                                                                           10)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           4
                                                                                                                           3)) == (0b00#2 : (BitVec 2))))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__418 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__418 <b 2403) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__419 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 2403
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
                                                                                                              (decode_FMLA_ZA_ZZV_4x1
                                                                                                                sz
                                                                                                                Zm
                                                                                                                Rv
                                                                                                                Zn
                                                                                                                S
                                                                                                                off3)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__421 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         23)) == (0b110000010#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           21
                                                                                                                           20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             15
                                                                                                                             15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               12
                                                                                                                               10)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               4
                                                                                                                               3)) == (0b01#2 : (BitVec 2))))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__420 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__420 <b 2404) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__421 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 2404
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
                                                                                                                  (decode_FMLS_ZA_ZZV_4x1
                                                                                                                    sz
                                                                                                                    Zm
                                                                                                                    Rv
                                                                                                                    Zn
                                                                                                                    S
                                                                                                                    off3)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__423 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               15
                                                                                                                               15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 12
                                                                                                                                 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 5
                                                                                                                                 3)) == (0b000#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__422 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__422 <b 2405) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__423 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 2405
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
                                                                                                                      let i2 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          10
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
                                                                                                                      (decode_FMLA_ZA_ZZi_S2xi
                                                                                                                        Zm
                                                                                                                        Rv
                                                                                                                        i2
                                                                                                                        Zn
                                                                                                                        S
                                                                                                                        off3)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__425 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   15
                                                                                                                                   15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     12
                                                                                                                                     12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     5
                                                                                                                                     3)) == (0b010#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__424 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__424 <b 2406) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__425 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 2406
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
                                                                                                                          let i2 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              10
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
                                                                                                                          (decode_FMLS_ZA_ZZi_S2xi
                                                                                                                            Zm
                                                                                                                            Rv
                                                                                                                            i2
                                                                                                                            Zn
                                                                                                                            S
                                                                                                                            off3)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__427 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     20)) == (0xC1D#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         12
                                                                                                                                         11)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         5
                                                                                                                                         3)) == (0b000#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__426 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__426 <b 2407) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__427 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 2407
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
                                                                                                                              let i1 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  10
                                                                                                                                  1)
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
                                                                                                                              (decode_FMLA_ZA_ZZi_D2xi
                                                                                                                                Zm
                                                                                                                                Rv
                                                                                                                                i1
                                                                                                                                Zn
                                                                                                                                S
                                                                                                                                off3)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__429 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         20)) == (0xC1D#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           15
                                                                                                                                           15)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             12
                                                                                                                                             11)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             5
                                                                                                                                             3)) == (0b010#3 : (BitVec 3)))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__428 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__428 <b 2408) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__429 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 2408
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
                                                                                                                                  let i1 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      10
                                                                                                                                      1)
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
                                                                                                                                  (decode_FMLS_ZA_ZZi_D2xi
                                                                                                                                    Zm
                                                                                                                                    Rv
                                                                                                                                    i1
                                                                                                                                    Zn
                                                                                                                                    S
                                                                                                                                    off3)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__431 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             20)) == (0xC15#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               15
                                                                                                                                               15)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 12
                                                                                                                                                 12)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 6
                                                                                                                                                 3)) == (0x0#4 : (BitVec 4)))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__430 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__430 <b 2409) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__431 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 2409
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
                                                                                                                                      let i2 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          10
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
                                                                                                                                      (decode_FMLA_ZA_ZZi_S4xi
                                                                                                                                        Zm
                                                                                                                                        Rv
                                                                                                                                        i2
                                                                                                                                        Zn
                                                                                                                                        S
                                                                                                                                        off3)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (pure true)))))))))))))))))))))))))))))))))


end ArmFull.Functions
