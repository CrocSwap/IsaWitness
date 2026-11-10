import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0985
import ArmFull.Fn.M1161
import ArmFull.Fn.M1338
import ArmFull.Fn.M1339
import ArmFull.Fn.M1340

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
def __DecodeA64_SME__seg1 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__75 ← (( do
    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xA04#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
               __opcode 15 13)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
               __opcode 1 0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
    then
      (do
        let w__74 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__74 <b 2231) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__75 : Bool)
  then
    (do
      writeReg SEE 2231
      let imm4 := (BitVec.slice __opcode 16 4)
      let msz := (BitVec.slice __opcode 13 2)
      let PNg := (BitVec.slice __opcode 10 3)
      let Rn := (BitVec.slice __opcode 5 5)
      let Zt := (BitVec.slice __opcode 2 3)
      let N := (BitVec.slice __opcode 0 1)
      (decode_LD1H_MZ_P_BI_4 imm4 msz PNg Rn Zt N)
      (pure false))
  else
    (do
      let w__77 ← (( do
        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xA04#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                   __opcode 15 13)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                   __opcode 1 0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
        then
          (do
            let w__76 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__76 <b 2232) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__77 : Bool)
      then
        (do
          writeReg SEE 2232
          let imm4 := (BitVec.slice __opcode 16 4)
          let msz := (BitVec.slice __opcode 13 2)
          let PNg := (BitVec.slice __opcode 10 3)
          let Rn := (BitVec.slice __opcode 5 5)
          let Zt := (BitVec.slice __opcode 2 3)
          let N := (BitVec.slice __opcode 0 1)
          (decode_LD1W_MZ_P_BI_4 imm4 msz PNg Rn Zt N)
          (pure false))
      else
        (do
          let w__79 ← (( do
            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xA04#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                       __opcode 15 13)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                       __opcode 1 0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
            then
              (do
                let w__78 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__78 <b 2233) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__79 : Bool)
          then
            (do
              writeReg SEE 2233
              let imm4 := (BitVec.slice __opcode 16 4)
              let msz := (BitVec.slice __opcode 13 2)
              let PNg := (BitVec.slice __opcode 10 3)
              let Rn := (BitVec.slice __opcode 5 5)
              let Zt := (BitVec.slice __opcode 2 3)
              let N := (BitVec.slice __opcode 0 1)
              (decode_LD1D_MZ_P_BI_4 imm4 msz PNg Rn Zt N)
              (pure false))
          else
            (do
              let w__81 ← (( do
                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xA04#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                           __opcode 15 13)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 0 0)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                then
                  (do
                    let w__80 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__80 <b 2234) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__81 : Bool)
              then
                (do
                  writeReg SEE 2234
                  let imm4 := (BitVec.slice __opcode 16 4)
                  let msz := (BitVec.slice __opcode 13 2)
                  let PNg := (BitVec.slice __opcode 10 3)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let Zt := (BitVec.slice __opcode 1 4)
                  let N := (BitVec.slice __opcode 0 1)
                  (decode_LDNT1B_MZ_P_BI_2 imm4 msz PNg Rn Zt N)
                  (pure false))
              else
                (do
                  let w__83 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xA04#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                               __opcode 15 13)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 0 0)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                    then
                      (do
                        let w__82 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__82 <b 2235) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__83 : Bool)
                  then
                    (do
                      writeReg SEE 2235
                      let imm4 := (BitVec.slice __opcode 16 4)
                      let msz := (BitVec.slice __opcode 13 2)
                      let PNg := (BitVec.slice __opcode 10 3)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let Zt := (BitVec.slice __opcode 1 4)
                      let N := (BitVec.slice __opcode 0 1)
                      (decode_LDNT1H_MZ_P_BI_2 imm4 msz PNg Rn Zt N)
                      (pure false))
                  else
                    (do
                      let w__85 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31
                                 20)) == (0xA04#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                   __opcode 15 13)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                   __opcode 0 0)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                        then
                          (do
                            let w__84 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__84 <b 2236) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__85 : Bool)
                      then
                        (do
                          writeReg SEE 2236
                          let imm4 := (BitVec.slice __opcode 16 4)
                          let msz := (BitVec.slice __opcode 13 2)
                          let PNg := (BitVec.slice __opcode 10 3)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let Zt := (BitVec.slice __opcode 1 4)
                          let N := (BitVec.slice __opcode 0 1)
                          (decode_LDNT1W_MZ_P_BI_2 imm4 msz PNg Rn Zt N)
                          (pure false))
                      else
                        (do
                          let w__87 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode
                                     31 20)) == (0xA04#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                       __opcode 15 13)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 0 0)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                            then
                              (do
                                let w__86 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__86 <b 2237) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__87 : Bool)
                          then
                            (do
                              writeReg SEE 2237
                              let imm4 := (BitVec.slice __opcode 16 4)
                              let msz := (BitVec.slice __opcode 13 2)
                              let PNg := (BitVec.slice __opcode 10 3)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let Zt := (BitVec.slice __opcode 1 4)
                              let N := (BitVec.slice __opcode 0 1)
                              (decode_LDNT1D_MZ_P_BI_2 imm4 msz PNg Rn Zt N)
                              (pure false))
                          else
                            (do
                              let w__89 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                         __opcode 31 20)) == (0xA04#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                           __opcode 15 13)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                           __opcode 1 0)) == (0b01#2 : (BitVec 2))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__88 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__88 <b 2238) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__89 : Bool)
                              then
                                (do
                                  writeReg SEE 2238
                                  let imm4 := (BitVec.slice __opcode 16 4)
                                  let msz := (BitVec.slice __opcode 13 2)
                                  let PNg := (BitVec.slice __opcode 10 3)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let Zt := (BitVec.slice __opcode 2 3)
                                  let N := (BitVec.slice __opcode 0 1)
                                  (decode_LDNT1B_MZ_P_BI_4 imm4 msz PNg Rn Zt N)
                                  (pure false))
                              else
                                (do
                                  let w__91 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                             __opcode 31 20)) == (0xA04#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                               __opcode 15 13)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                               __opcode 1 0)) == (0b01#2 : (BitVec 2))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__90 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__90 <b 2239) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__91 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2239
                                      let imm4 := (BitVec.slice __opcode 16 4)
                                      let msz := (BitVec.slice __opcode 13 2)
                                      let PNg := (BitVec.slice __opcode 10 3)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let Zt := (BitVec.slice __opcode 2 3)
                                      let N := (BitVec.slice __opcode 0 1)
                                      (decode_LDNT1H_MZ_P_BI_4 imm4 msz PNg Rn Zt N)
                                      (pure false))
                                  else
                                    (do
                                      let w__93 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                 __opcode 31 20)) == (0xA04#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                   __opcode 15 13)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                   __opcode 1 0)) == (0b01#2 : (BitVec 2))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__92 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__92 <b 2240) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__93 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2240
                                          let imm4 := (BitVec.slice __opcode 16 4)
                                          let msz := (BitVec.slice __opcode 13 2)
                                          let PNg := (BitVec.slice __opcode 10 3)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let Zt := (BitVec.slice __opcode 2 3)
                                          let N := (BitVec.slice __opcode 0 1)
                                          (decode_LDNT1W_MZ_P_BI_4 imm4 msz PNg Rn Zt N)
                                          (pure false))
                                      else
                                        (do
                                          let w__95 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                     __opcode 31 20)) == (0xA04#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                       __opcode 15 13)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                       __opcode 1 0)) == (0b01#2 : (BitVec 2))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__94 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__94 <b 2241) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__95 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2241
                                              let imm4 := (BitVec.slice __opcode 16 4)
                                              let msz := (BitVec.slice __opcode 13 2)
                                              let PNg := (BitVec.slice __opcode 10 3)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let Zt := (BitVec.slice __opcode 2 3)
                                              let N := (BitVec.slice __opcode 0 1)
                                              (decode_LDNT1D_MZ_P_BI_4 imm4 msz PNg Rn Zt N)
                                              (pure false))
                                          else
                                            (do
                                              let w__97 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                         __opcode 31 20)) == (0xA06#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                           __opcode 15 13)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 0 0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__96 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__96 <b 2242) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__97 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2242
                                                  let imm4 := (BitVec.slice __opcode 16 4)
                                                  let msz := (BitVec.slice __opcode 13 2)
                                                  let PNg := (BitVec.slice __opcode 10 3)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let Zt := (BitVec.slice __opcode 1 4)
                                                  let N := (BitVec.slice __opcode 0 1)
                                                  (decode_ST1B_MZ_P_BI_2 imm4 msz PNg Rn Zt N)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__99 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                             __opcode 31 20)) == (0xA06#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                               __opcode 15 13)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 0 0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__98 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__98 <b 2243) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__99 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2243
                                                      let imm4 := (BitVec.slice __opcode 16 4)
                                                      let msz := (BitVec.slice __opcode 13 2)
                                                      let PNg := (BitVec.slice __opcode 10 3)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let Zt := (BitVec.slice __opcode 1 4)
                                                      let N := (BitVec.slice __opcode 0 1)
                                                      (decode_ST1H_MZ_P_BI_2 imm4 msz PNg Rn Zt N)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__101 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                 __opcode 31 20)) == (0xA06#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                   __opcode 15 13)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 0 0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__100 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__100 <b 2244) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__101 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2244
                                                          let imm4 := (BitVec.slice __opcode 16 4)
                                                          let msz := (BitVec.slice __opcode 13 2)
                                                          let PNg := (BitVec.slice __opcode 10 3)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let Zt := (BitVec.slice __opcode 1 4)
                                                          let N := (BitVec.slice __opcode 0 1)
                                                          (decode_ST1W_MZ_P_BI_2 imm4 msz PNg Rn Zt
                                                            N)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__103 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                     __opcode 31 20)) == (0xA06#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                       __opcode 15 13)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 0 0)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__102 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__102 <b 2245) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__103 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2245
                                                              let imm4 :=
                                                                (BitVec.slice __opcode 16 4)
                                                              let msz :=
                                                                (BitVec.slice __opcode 13 2)
                                                              let PNg :=
                                                                (BitVec.slice __opcode 10 3)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let Zt := (BitVec.slice __opcode 1 4)
                                                              let N := (BitVec.slice __opcode 0 1)
                                                              (decode_ST1D_MZ_P_BI_2 imm4 msz PNg Rn
                                                                Zt N)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__105 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                         __opcode 31 20)) == (0xA06#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                           __opcode 15 13)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                           __opcode 1 0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__104 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__104 <b 2246) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__105 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2246
                                                                  let imm4 :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let msz :=
                                                                    (BitVec.slice __opcode 13 2)
                                                                  let PNg :=
                                                                    (BitVec.slice __opcode 10 3)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let Zt :=
                                                                    (BitVec.slice __opcode 2 3)
                                                                  let N :=
                                                                    (BitVec.slice __opcode 0 1)
                                                                  (decode_ST1B_MZ_P_BI_4 imm4 msz
                                                                    PNg Rn Zt N)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__107 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                             __opcode 31 20)) == (0xA06#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                               __opcode 15 13)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                               __opcode 1 0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__106 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__106 <b 2247) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__107 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2247
                                                                      let imm4 :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let msz :=
                                                                        (BitVec.slice __opcode 13 2)
                                                                      let PNg :=
                                                                        (BitVec.slice __opcode 10 3)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let Zt :=
                                                                        (BitVec.slice __opcode 2 3)
                                                                      let N :=
                                                                        (BitVec.slice __opcode 0 1)
                                                                      (decode_ST1H_MZ_P_BI_4 imm4
                                                                        msz PNg Rn Zt N)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__109 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 20)) == (0xA06#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                   __opcode 15 13)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                   __opcode 1 0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__108 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__108 <b 2248) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__109 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2248
                                                                          let imm4 :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let msz :=
                                                                            (BitVec.slice __opcode
                                                                              13 2)
                                                                          let PNg :=
                                                                            (BitVec.slice __opcode
                                                                              10 3)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let Zt :=
                                                                            (BitVec.slice __opcode 2
                                                                              3)
                                                                          let N :=
                                                                            (BitVec.slice __opcode 0
                                                                              1)
                                                                          (decode_ST1W_MZ_P_BI_4
                                                                            imm4 msz PNg Rn Zt N)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__111 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 20)) == (0xA06#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                       __opcode 15
                                                                                       13)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                       __opcode 1 0)) == (0b00#2 : (BitVec 2))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__110 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__110 <b 2249) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__111 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2249
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
                                                                              let Zt :=
                                                                                (BitVec.slice
                                                                                  __opcode 2 3)
                                                                              let N :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 1)
                                                                              (decode_ST1D_MZ_P_BI_4
                                                                                imm4 msz PNg Rn Zt N)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__113 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         20)) == (0xA06#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           15 13)) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           0 0)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__112 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__112 <b 2250) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__113 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2250
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
                                                                                  let Zt :=
                                                                                    (BitVec.slice
                                                                                      __opcode 1 4)
                                                                                  let N :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 1)
                                                                                  (decode_STNT1B_MZ_P_BI_2
                                                                                    imm4 msz PNg Rn
                                                                                    Zt N)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__115 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 20)) == (0xA06#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               15 13)) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               0 0)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__114 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__114 <b 2251) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__115 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2251
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
                                                                                      let Zt :=
                                                                                        (BitVec.slice
                                                                                          __opcode 1
                                                                                          4)
                                                                                      let N :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          1)
                                                                                      (decode_STNT1H_MZ_P_BI_2
                                                                                        imm4 msz PNg
                                                                                        Rn Zt N)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__117 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 20)) == (0xA06#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   15
                                                                                                   13)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   0
                                                                                                   0)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__116 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__116 <b 2252) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__117 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2252
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
                                                                                          let Zt :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              1 4)
                                                                                          let N :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 1)
                                                                                          (decode_STNT1W_MZ_P_BI_2
                                                                                            imm4 msz
                                                                                            PNg Rn
                                                                                            Zt N)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__119 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     20)) == (0xA06#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       15
                                                                                                       13)) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       0
                                                                                                       0)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__118 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__118 <b 2253) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__119 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2253
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
                                                                                              let Zt :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  1
                                                                                                  4)
                                                                                              let N :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  1)
                                                                                              (decode_STNT1D_MZ_P_BI_2
                                                                                                imm4
                                                                                                msz
                                                                                                PNg
                                                                                                Rn
                                                                                                Zt N)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__121 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         20)) == (0xA06#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           15
                                                                                                           13)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           1
                                                                                                           0)) == (0b01#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__120 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__120 <b 2254) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__121 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2254
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
                                                                                                  let Zt :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      2
                                                                                                      3)
                                                                                                  let N :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      1)
                                                                                                  (decode_STNT1B_MZ_P_BI_4
                                                                                                    imm4
                                                                                                    msz
                                                                                                    PNg
                                                                                                    Rn
                                                                                                    Zt
                                                                                                    N)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__123 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             20)) == (0xA06#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               13)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               1
                                                                                                               0)) == (0b01#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__122 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__122 <b 2255) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__123 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 2255
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
                                                                                                      let Zt :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          2
                                                                                                          3)
                                                                                                      let N :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          1)
                                                                                                      (decode_STNT1H_MZ_P_BI_4
                                                                                                        imm4
                                                                                                        msz
                                                                                                        PNg
                                                                                                        Rn
                                                                                                        Zt
                                                                                                        N)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__125 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 20)) == (0xA06#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   15
                                                                                                                   13)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   1
                                                                                                                   0)) == (0b01#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__124 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__124 <b 2256) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__125 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 2256
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
                                                                                                          let Zt :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              2
                                                                                                              3)
                                                                                                          let N :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              1)
                                                                                                          (decode_STNT1W_MZ_P_BI_4
                                                                                                            imm4
                                                                                                            msz
                                                                                                            PNg
                                                                                                            Rn
                                                                                                            Zt
                                                                                                            N)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__127 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     20)) == (0xA06#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       15
                                                                                                                       13)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       1
                                                                                                                       0)) == (0b01#2 : (BitVec 2))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__126 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__126 <b 2257) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__127 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 2257
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
                                                                                                              let Zt :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  2
                                                                                                                  3)
                                                                                                              let N :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  1)
                                                                                                              (decode_STNT1D_MZ_P_BI_4
                                                                                                                imm4
                                                                                                                msz
                                                                                                                PNg
                                                                                                                Rn
                                                                                                                Zt
                                                                                                                N)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__129 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         21)) == (0b10000000100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         4
                                                                                                                         2)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__128 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__128 <b 2258) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__129 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 2258
                                                                                                                  let Zm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      5)
                                                                                                                  let Pm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      13
                                                                                                                      3)
                                                                                                                  let Pn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      10
                                                                                                                      3)
                                                                                                                  let Zn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      5
                                                                                                                      5)
                                                                                                                  let S :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      4
                                                                                                                      1)
                                                                                                                  let ZAda :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      2)
                                                                                                                  (decode_FMOPA_ZA_PP_ZZ_32
                                                                                                                    Zm
                                                                                                                    Pm
                                                                                                                    Pn
                                                                                                                    Zn
                                                                                                                    S
                                                                                                                    ZAda)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__131 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             21)) == (0b10000000100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             4
                                                                                                                             2)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__130 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__130 <b 2259) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__131 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 2259
                                                                                                                      let Zm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          5)
                                                                                                                      let Pm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          13
                                                                                                                          3)
                                                                                                                      let Pn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          10
                                                                                                                          3)
                                                                                                                      let Zn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          5
                                                                                                                          5)
                                                                                                                      let S :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          4
                                                                                                                          1)
                                                                                                                      let ZAda :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          2)
                                                                                                                      (decode_FMOPS_ZA_PP_ZZ_32
                                                                                                                        Zm
                                                                                                                        Pm
                                                                                                                        Pn
                                                                                                                        Zn
                                                                                                                        S
                                                                                                                        ZAda)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__133 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 21)) == (0b10000000110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 4
                                                                                                                                 3)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__132 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__132 <b 2260) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__133 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 2260
                                                                                                                          let Zm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              5)
                                                                                                                          let Pm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              13
                                                                                                                              3)
                                                                                                                          let Pn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              10
                                                                                                                              3)
                                                                                                                          let Zn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              5
                                                                                                                              5)
                                                                                                                          let S :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              4
                                                                                                                              1)
                                                                                                                          let ZAda :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              3)
                                                                                                                          (decode_FMOPA_ZA_PP_ZZ_64
                                                                                                                            Zm
                                                                                                                            Pm
                                                                                                                            Pn
                                                                                                                            Zn
                                                                                                                            S
                                                                                                                            ZAda)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__135 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     21)) == (0b10000000110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     4
                                                                                                                                     3)) == (0b10#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__134 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__134 <b 2261) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__135 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 2261
                                                                                                                              let Zm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  5)
                                                                                                                              let Pm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  13
                                                                                                                                  3)
                                                                                                                              let Pn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  10
                                                                                                                                  3)
                                                                                                                              let Zn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  5
                                                                                                                                  5)
                                                                                                                              let S :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  4
                                                                                                                                  1)
                                                                                                                              let ZAda :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  3)
                                                                                                                              (decode_FMOPS_ZA_PP_ZZ_64
                                                                                                                                Zm
                                                                                                                                Pm
                                                                                                                                Pn
                                                                                                                                Zn
                                                                                                                                S
                                                                                                                                ZAda)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__137 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         21)) == (0b10000001100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         4
                                                                                                                                         2)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__136 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__136 <b 2262) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__137 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 2262
                                                                                                                                  let Zm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      5)
                                                                                                                                  let Pm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      13
                                                                                                                                      3)
                                                                                                                                  let Pn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      10
                                                                                                                                      3)
                                                                                                                                  let Zn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      5
                                                                                                                                      5)
                                                                                                                                  let S :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      4
                                                                                                                                      1)
                                                                                                                                  let ZAda :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      2)
                                                                                                                                  (decode_BFMOPA_ZA32_PP_ZZ__
                                                                                                                                    Zm
                                                                                                                                    Pm
                                                                                                                                    Pn
                                                                                                                                    Zn
                                                                                                                                    S
                                                                                                                                    ZAda)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__139 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             21)) == (0b10000001100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             4
                                                                                                                                             2)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__138 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__138 <b 2263) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__139 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 2263
                                                                                                                                      let Zm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          5)
                                                                                                                                      let Pm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          13
                                                                                                                                          3)
                                                                                                                                      let Pn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          10
                                                                                                                                          3)
                                                                                                                                      let Zn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          5
                                                                                                                                          5)
                                                                                                                                      let S :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          4
                                                                                                                                          1)
                                                                                                                                      let ZAda :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          2)
                                                                                                                                      (decode_BFMOPS_ZA32_PP_ZZ__
                                                                                                                                        Zm
                                                                                                                                        Pm
                                                                                                                                        Pn
                                                                                                                                        Zn
                                                                                                                                        S
                                                                                                                                        ZAda)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__141 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 21)) == (0b10000001101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 4
                                                                                                                                                 2)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__140 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__140 <b 2264) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__141 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 2264
                                                                                                                                          let Zm :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              5)
                                                                                                                                          let Pm :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              13
                                                                                                                                              3)
                                                                                                                                          let Pn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              10
                                                                                                                                              3)
                                                                                                                                          let Zn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              5)
                                                                                                                                          let S :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              4
                                                                                                                                              1)
                                                                                                                                          let ZAda :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              2)
                                                                                                                                          (decode_FMOPA_ZA32_PP_ZZ_16
                                                                                                                                            Zm
                                                                                                                                            Pm
                                                                                                                                            Pn
                                                                                                                                            Zn
                                                                                                                                            S
                                                                                                                                            ZAda)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__143 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     21)) == (0b10000001101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     4
                                                                                                                                                     2)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__142 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__142 <b 2265) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__143 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 2265
                                                                                                                                              let Zm :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  5)
                                                                                                                                              let Pm :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  13
                                                                                                                                                  3)
                                                                                                                                              let Pn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  10
                                                                                                                                                  3)
                                                                                                                                              let Zn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  5
                                                                                                                                                  5)
                                                                                                                                              let S :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  4
                                                                                                                                                  1)
                                                                                                                                              let ZAda :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  2)
                                                                                                                                              (decode_FMOPS_ZA32_PP_ZZ_16
                                                                                                                                                Zm
                                                                                                                                                Pm
                                                                                                                                                Pn
                                                                                                                                                Zn
                                                                                                                                                S
                                                                                                                                                ZAda)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__145 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         21)) == (0b10100000100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         4
                                                                                                                                                         2)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__144 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__144 <b 2266) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__145 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 2266
                                                                                                                                                  let u0 :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      24
                                                                                                                                                      1)
                                                                                                                                                  let u1 :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      21
                                                                                                                                                      1)
                                                                                                                                                  let Zm :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      16
                                                                                                                                                      5)
                                                                                                                                                  let Pm :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      13
                                                                                                                                                      3)
                                                                                                                                                  let Pn :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      10
                                                                                                                                                      3)
                                                                                                                                                  let Zn :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      5
                                                                                                                                                      5)
                                                                                                                                                  let S :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      4
                                                                                                                                                      1)
                                                                                                                                                  let ZAda :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      2)
                                                                                                                                                  (decode_SMOPA_ZA_PP_ZZ_32
                                                                                                                                                    u0
                                                                                                                                                    u1
                                                                                                                                                    Zm
                                                                                                                                                    Pm
                                                                                                                                                    Pn
                                                                                                                                                    Zn
                                                                                                                                                    S
                                                                                                                                                    ZAda)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__147 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             21)) == (0b10100000101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             4
                                                                                                                                                             2)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__146 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__146 <b 2267) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__147 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 2267
                                                                                                                                                      let u0 :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          24
                                                                                                                                                          1)
                                                                                                                                                      let u1 :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          21
                                                                                                                                                          1)
                                                                                                                                                      let Zm :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          16
                                                                                                                                                          5)
                                                                                                                                                      let Pm :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          13
                                                                                                                                                          3)
                                                                                                                                                      let Pn :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          10
                                                                                                                                                          3)
                                                                                                                                                      let Zn :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          5
                                                                                                                                                          5)
                                                                                                                                                      let S :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          4
                                                                                                                                                          1)
                                                                                                                                                      let ZAda :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          2)
                                                                                                                                                      (decode_SUMOPA_ZA_PP_ZZ_32
                                                                                                                                                        u0
                                                                                                                                                        u1
                                                                                                                                                        Zm
                                                                                                                                                        Pm
                                                                                                                                                        Pn
                                                                                                                                                        Zn
                                                                                                                                                        S
                                                                                                                                                        ZAda)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (pure true)))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
