import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1332
import ArmFull.Fn.M1333
import ArmFull.Fn.M1334
import ArmFull.Fn.M1335

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
def __DecodeA64_SVE__seg27 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__2193 ← (( do
    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11100101011#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 15 15)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 13 13)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
    then
      (do
        let w__2192 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__2192 <b 2133) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2193 : Bool)
  then
    (do
      writeReg SEE 2133
      let msz := (BitVec.slice __opcode 23 2)
      let Zm := (BitVec.slice __opcode 16 5)
      let xs := (BitVec.slice __opcode 14 1)
      let Pg := (BitVec.slice __opcode 10 3)
      let Rn := (BitVec.slice __opcode 5 5)
      let Zt := (BitVec.slice __opcode 0 5)
      (decode_ST1W_Z_P_BZ_S_x32_scaled msz Zm xs Pg Rn Zt)
      (pure false))
  else
    (do
      let w__2195 ← (( do
        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11100100000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                 __opcode 15 13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
        then
          (do
            let w__2194 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__2194 <b 2134) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__2195 : Bool)
      then
        (do
          writeReg SEE 2134
          let msz := (BitVec.slice __opcode 23 2)
          let Zm := (BitVec.slice __opcode 16 5)
          let Pg := (BitVec.slice __opcode 10 3)
          let Rn := (BitVec.slice __opcode 5 5)
          let Zt := (BitVec.slice __opcode 0 5)
          (decode_ST1B_Z_P_BZ_D_64_unscaled msz Zm Pg Rn Zt)
          (pure false))
      else
        (do
          let w__2197 ← (( do
            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11100100100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                     __opcode 15 13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
            then
              (do
                let w__2196 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__2196 <b 2135) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__2197 : Bool)
          then
            (do
              writeReg SEE 2135
              let msz := (BitVec.slice __opcode 23 2)
              let Zm := (BitVec.slice __opcode 16 5)
              let Pg := (BitVec.slice __opcode 10 3)
              let Rn := (BitVec.slice __opcode 5 5)
              let Zt := (BitVec.slice __opcode 0 5)
              (decode_ST1H_Z_P_BZ_D_64_unscaled msz Zm Pg Rn Zt)
              (pure false))
          else
            (do
              let w__2199 ← (( do
                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11100101000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                         __opcode 15 13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                then
                  (do
                    let w__2198 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__2198 <b 2136) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__2199 : Bool)
              then
                (do
                  writeReg SEE 2136
                  let msz := (BitVec.slice __opcode 23 2)
                  let Zm := (BitVec.slice __opcode 16 5)
                  let Pg := (BitVec.slice __opcode 10 3)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let Zt := (BitVec.slice __opcode 0 5)
                  (decode_ST1W_Z_P_BZ_D_64_unscaled msz Zm Pg Rn Zt)
                  (pure false))
              else
                (do
                  let w__2201 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11100101100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                             __opcode 15 13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                    then
                      (do
                        let w__2200 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__2200 <b 2137) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__2201 : Bool)
                  then
                    (do
                      writeReg SEE 2137
                      let msz := (BitVec.slice __opcode 23 2)
                      let Zm := (BitVec.slice __opcode 16 5)
                      let Pg := (BitVec.slice __opcode 10 3)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let Zt := (BitVec.slice __opcode 0 5)
                      (decode_ST1D_Z_P_BZ_D_64_unscaled msz Zm Pg Rn Zt)
                      (pure false))
                  else
                    (do
                      let w__2203 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31
                                 21)) == (0b11100100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                 __opcode 15 13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                        then
                          (do
                            let w__2202 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__2202 <b 2138) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__2203 : Bool)
                      then
                        (do
                          writeReg SEE 2138
                          let msz := (BitVec.slice __opcode 23 2)
                          let Zm := (BitVec.slice __opcode 16 5)
                          let Pg := (BitVec.slice __opcode 10 3)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let Zt := (BitVec.slice __opcode 0 5)
                          (decode_ST1H_Z_P_BZ_D_64_scaled msz Zm Pg Rn Zt)
                          (pure false))
                      else
                        (do
                          let w__2205 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode
                                     31 21)) == (0b11100101001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                     __opcode 15 13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                            then
                              (do
                                let w__2204 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__2204 <b 2139) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__2205 : Bool)
                          then
                            (do
                              writeReg SEE 2139
                              let msz := (BitVec.slice __opcode 23 2)
                              let Zm := (BitVec.slice __opcode 16 5)
                              let Pg := (BitVec.slice __opcode 10 3)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let Zt := (BitVec.slice __opcode 0 5)
                              (decode_ST1W_Z_P_BZ_D_64_scaled msz Zm Pg Rn Zt)
                              (pure false))
                          else
                            (do
                              let w__2207 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                         __opcode 31 21)) == (0b11100101101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                         __opcode 15 13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__2206 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__2206 <b 2140) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__2207 : Bool)
                              then
                                (do
                                  writeReg SEE 2140
                                  let msz := (BitVec.slice __opcode 23 2)
                                  let Zm := (BitVec.slice __opcode 16 5)
                                  let Pg := (BitVec.slice __opcode 10 3)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let Zt := (BitVec.slice __opcode 0 5)
                                  (decode_ST1D_Z_P_BZ_D_64_scaled msz Zm Pg Rn Zt)
                                  (pure false))
                              else
                                (do
                                  let w__2209 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                             __opcode 31 21)) == (0b11100100010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                             __opcode 15 13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__2208 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__2208 <b 2141) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__2209 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2141
                                      let msz := (BitVec.slice __opcode 23 2)
                                      let imm5 := (BitVec.slice __opcode 16 5)
                                      let Pg := (BitVec.slice __opcode 10 3)
                                      let Zn := (BitVec.slice __opcode 5 5)
                                      let Zt := (BitVec.slice __opcode 0 5)
                                      (decode_ST1B_Z_P_AI_D msz imm5 Pg Zn Zt)
                                      (pure false))
                                  else
                                    (do
                                      let w__2211 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                 __opcode 31 21)) == (0b11100100110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                 __opcode 15 13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__2210 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__2210 <b 2142) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__2211 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2142
                                          let msz := (BitVec.slice __opcode 23 2)
                                          let imm5 := (BitVec.slice __opcode 16 5)
                                          let Pg := (BitVec.slice __opcode 10 3)
                                          let Zn := (BitVec.slice __opcode 5 5)
                                          let Zt := (BitVec.slice __opcode 0 5)
                                          (decode_ST1H_Z_P_AI_D msz imm5 Pg Zn Zt)
                                          (pure false))
                                      else
                                        (do
                                          let w__2213 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                     __opcode 31 21)) == (0b11100101010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                     __opcode 15 13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__2212 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__2212 <b 2143) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__2213 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2143
                                              let msz := (BitVec.slice __opcode 23 2)
                                              let imm5 := (BitVec.slice __opcode 16 5)
                                              let Pg := (BitVec.slice __opcode 10 3)
                                              let Zn := (BitVec.slice __opcode 5 5)
                                              let Zt := (BitVec.slice __opcode 0 5)
                                              (decode_ST1W_Z_P_AI_D msz imm5 Pg Zn Zt)
                                              (pure false))
                                          else
                                            (do
                                              let w__2215 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                         __opcode 31 21)) == (0b11100101110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                         __opcode 15 13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__2214 ← (( do readReg SEE ) : SailM Int
                                                      )
                                                    (pure (((w__2214 <b 2144) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__2215 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2144
                                                  let msz := (BitVec.slice __opcode 23 2)
                                                  let imm5 := (BitVec.slice __opcode 16 5)
                                                  let Pg := (BitVec.slice __opcode 10 3)
                                                  let Zn := (BitVec.slice __opcode 5 5)
                                                  let Zt := (BitVec.slice __opcode 0 5)
                                                  (decode_ST1D_Z_P_AI_D msz imm5 Pg Zn Zt)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__2217 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                             __opcode 31 21)) == (0b11100100011#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                             __opcode 15 13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__2216 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__2216 <b 2145) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__2217 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2145
                                                      let msz := (BitVec.slice __opcode 23 2)
                                                      let imm5 := (BitVec.slice __opcode 16 5)
                                                      let Pg := (BitVec.slice __opcode 10 3)
                                                      let Zn := (BitVec.slice __opcode 5 5)
                                                      let Zt := (BitVec.slice __opcode 0 5)
                                                      (decode_ST1B_Z_P_AI_S msz imm5 Pg Zn Zt)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__2219 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                 __opcode 31 21)) == (0b11100100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                 __opcode 15 13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__2218 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__2218 <b 2146) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__2219 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2146
                                                          let msz := (BitVec.slice __opcode 23 2)
                                                          let imm5 := (BitVec.slice __opcode 16 5)
                                                          let Pg := (BitVec.slice __opcode 10 3)
                                                          let Zn := (BitVec.slice __opcode 5 5)
                                                          let Zt := (BitVec.slice __opcode 0 5)
                                                          (decode_ST1H_Z_P_AI_S msz imm5 Pg Zn Zt)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__2221 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                     __opcode 31 21)) == (0b11100101011#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                     __opcode 15 13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__2220 ← (( do readReg SEE )
                                                                  : SailM Int )
                                                                (pure (((w__2220 <b 2147) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__2221 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2147
                                                              let msz :=
                                                                (BitVec.slice __opcode 23 2)
                                                              let imm5 :=
                                                                (BitVec.slice __opcode 16 5)
                                                              let Pg := (BitVec.slice __opcode 10 3)
                                                              let Zn := (BitVec.slice __opcode 5 5)
                                                              let Zt := (BitVec.slice __opcode 0 5)
                                                              (decode_ST1W_Z_P_AI_S msz imm5 Pg Zn
                                                                Zt)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__2223 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                         __opcode 31 23)) == (0b111001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 20 20)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                           __opcode 15 13)) == (0b111#3 : (BitVec 3))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__2222 ← (( do
                                                                      readReg SEE ) : SailM Int )
                                                                    (pure (((w__2222 <b 2148) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__2223 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2148
                                                                  let msz :=
                                                                    (BitVec.slice __opcode 23 2)
                                                                  let size :=
                                                                    (BitVec.slice __opcode 21 2)
                                                                  let imm4 :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let Pg :=
                                                                    (BitVec.slice __opcode 10 3)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let Zt :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  (decode_ST1B_Z_P_BI__ msz size
                                                                    imm4 Pg Rn Zt)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__2225 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                             __opcode 31 23)) == (0b111001001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                               __opcode 20 20)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                               __opcode 15 13)) == (0b111#3 : (BitVec 3))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__2224 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__2224 <b 2149) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__2225 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2149
                                                                      let msz :=
                                                                        (BitVec.slice __opcode 23 2)
                                                                      let size :=
                                                                        (BitVec.slice __opcode 21 2)
                                                                      let imm4 :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let Pg :=
                                                                        (BitVec.slice __opcode 10 3)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let Zt :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      (decode_ST1H_Z_P_BI__ msz size
                                                                        imm4 Pg Rn Zt)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__2227 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 22)) == (0b1110010101#10 : (BitVec 10))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                   __opcode 20 20)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                   __opcode 15 13)) == (0b111#3 : (BitVec 3))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__2226 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__2226 <b 2150) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__2227 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2150
                                                                          let msz :=
                                                                            (BitVec.slice __opcode
                                                                              23 2)
                                                                          let sz :=
                                                                            (BitVec.slice __opcode
                                                                              21 1)
                                                                          let imm4 :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let Pg :=
                                                                            (BitVec.slice __opcode
                                                                              10 3)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let Zt :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          (decode_ST1W_Z_P_BI__ msz
                                                                            sz imm4 Pg Rn Zt)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__2229 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 20)) == (0xE5E#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                     __opcode 15 13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__2228 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__2228 <b 2151) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__2229 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2151
                                                                              let msz :=
                                                                                (BitVec.slice
                                                                                  __opcode 23 2)
                                                                              let imm4 :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let Pg :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 3)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let Zt :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              (decode_ST1D_Z_P_BI__
                                                                                msz imm4 Pg Rn Zt)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__2231 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         20)) == (0xE50#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                         __opcode 15
                                                                                         13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__2230 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__2230 <b 2152) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__2231 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2152
                                                                                  let msz :=
                                                                                    (BitVec.slice
                                                                                      __opcode 23 2)
                                                                                  let imm4 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Pg :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 3)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let Zt :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  (decode_ST1W_Z_P_BI_U128
                                                                                    msz imm4 Pg Rn
                                                                                    Zt)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__2233 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 20)) == (0xE5C#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             15 13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__2232 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__2232 <b 2153) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__2233 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2153
                                                                                      let msz :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          23 2)
                                                                                      let imm4 :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let Pg :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 3)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let Zt :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      (decode_ST1D_Z_P_BI_U128
                                                                                        msz imm4 Pg
                                                                                        Rn Zt)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__2235 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 20)) == (0xE41#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 15
                                                                                                 13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__2234 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__2234 <b 2154) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__2235 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2154
                                                                                          let msz :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              23 2)
                                                                                          let imm4 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Pg :=
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
                                                                                              0 5)
                                                                                          (decode_STNT1B_Z_P_BI_Contiguous
                                                                                            msz imm4
                                                                                            Pg Rn Zt)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__2237 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     20)) == (0xE49#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     15
                                                                                                     13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__2236 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__2236 <b 2155) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__2237 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2155
                                                                                              let msz :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  23
                                                                                                  2)
                                                                                              let imm4 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  4)
                                                                                              let Pg :=
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
                                                                                                  0
                                                                                                  5)
                                                                                              (decode_STNT1H_Z_P_BI_Contiguous
                                                                                                msz
                                                                                                imm4
                                                                                                Pg
                                                                                                Rn
                                                                                                Zt)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__2239 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         20)) == (0xE51#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         15
                                                                                                         13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__2238 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__2238 <b 2156) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__2239 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2156
                                                                                                  let msz :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      23
                                                                                                      2)
                                                                                                  let imm4 :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      4)
                                                                                                  let Pg :=
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
                                                                                                      0
                                                                                                      5)
                                                                                                  (decode_STNT1W_Z_P_BI_Contiguous
                                                                                                    msz
                                                                                                    imm4
                                                                                                    Pg
                                                                                                    Rn
                                                                                                    Zt)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__2241 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             20)) == (0xE59#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             15
                                                                                                             13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__2240 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__2240 <b 2157) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__2241 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 2157
                                                                                                      let msz :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          23
                                                                                                          2)
                                                                                                      let imm4 :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          4)
                                                                                                      let Pg :=
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
                                                                                                          0
                                                                                                          5)
                                                                                                      (decode_STNT1D_Z_P_BI_Contiguous
                                                                                                        msz
                                                                                                        imm4
                                                                                                        Pg
                                                                                                        Rn
                                                                                                        Zt)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__2243 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 20)) == (0xE43#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 15
                                                                                                                 13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__2242 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__2242 <b 2158) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__2243 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 2158
                                                                                                          let msz :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              23
                                                                                                              2)
                                                                                                          let imm4 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              4)
                                                                                                          let Pg :=
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
                                                                                                              0
                                                                                                              5)
                                                                                                          (decode_ST2B_Z_P_BI_Contiguous
                                                                                                            msz
                                                                                                            imm4
                                                                                                            Pg
                                                                                                            Rn
                                                                                                            Zt)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__2245 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     20)) == (0xE4B#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     15
                                                                                                                     13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__2244 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__2244 <b 2159) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__2245 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 2159
                                                                                                              let msz :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  23
                                                                                                                  2)
                                                                                                              let imm4 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  4)
                                                                                                              let Pg :=
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
                                                                                                                  0
                                                                                                                  5)
                                                                                                              (decode_ST2H_Z_P_BI_Contiguous
                                                                                                                msz
                                                                                                                imm4
                                                                                                                Pg
                                                                                                                Rn
                                                                                                                Zt)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__2247 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         20)) == (0xE53#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         15
                                                                                                                         13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__2246 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__2246 <b 2160) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__2247 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 2160
                                                                                                                  let msz :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      23
                                                                                                                      2)
                                                                                                                  let imm4 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      4)
                                                                                                                  let Pg :=
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
                                                                                                                      0
                                                                                                                      5)
                                                                                                                  (decode_ST2W_Z_P_BI_Contiguous
                                                                                                                    msz
                                                                                                                    imm4
                                                                                                                    Pg
                                                                                                                    Rn
                                                                                                                    Zt)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__2249 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             20)) == (0xE5B#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             15
                                                                                                                             13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__2248 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__2248 <b 2161) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__2249 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 2161
                                                                                                                      let msz :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          23
                                                                                                                          2)
                                                                                                                      let imm4 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          4)
                                                                                                                      let Pg :=
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
                                                                                                                          0
                                                                                                                          5)
                                                                                                                      (decode_ST2D_Z_P_BI_Contiguous
                                                                                                                        msz
                                                                                                                        imm4
                                                                                                                        Pg
                                                                                                                        Rn
                                                                                                                        Zt)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__2251 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 20)) == (0xE45#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 15
                                                                                                                                 13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__2250 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__2250 <b 2162) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__2251 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 2162
                                                                                                                          let msz :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              23
                                                                                                                              2)
                                                                                                                          let imm4 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              4)
                                                                                                                          let Pg :=
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
                                                                                                                              0
                                                                                                                              5)
                                                                                                                          (decode_ST3B_Z_P_BI_Contiguous
                                                                                                                            msz
                                                                                                                            imm4
                                                                                                                            Pg
                                                                                                                            Rn
                                                                                                                            Zt)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__2253 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     20)) == (0xE4D#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     15
                                                                                                                                     13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__2252 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__2252 <b 2163) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__2253 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 2163
                                                                                                                              let msz :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  23
                                                                                                                                  2)
                                                                                                                              let imm4 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  4)
                                                                                                                              let Pg :=
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
                                                                                                                                  0
                                                                                                                                  5)
                                                                                                                              (decode_ST3H_Z_P_BI_Contiguous
                                                                                                                                msz
                                                                                                                                imm4
                                                                                                                                Pg
                                                                                                                                Rn
                                                                                                                                Zt)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__2255 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         20)) == (0xE55#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         15
                                                                                                                                         13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__2254 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__2254 <b 2164) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__2255 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 2164
                                                                                                                                  let msz :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      23
                                                                                                                                      2)
                                                                                                                                  let imm4 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      4)
                                                                                                                                  let Pg :=
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
                                                                                                                                      0
                                                                                                                                      5)
                                                                                                                                  (decode_ST3W_Z_P_BI_Contiguous
                                                                                                                                    msz
                                                                                                                                    imm4
                                                                                                                                    Pg
                                                                                                                                    Rn
                                                                                                                                    Zt)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__2257 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             20)) == (0xE5D#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             15
                                                                                                                                             13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__2256 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__2256 <b 2165) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__2257 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 2165
                                                                                                                                      let msz :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          23
                                                                                                                                          2)
                                                                                                                                      let imm4 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          4)
                                                                                                                                      let Pg :=
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
                                                                                                                                          0
                                                                                                                                          5)
                                                                                                                                      (decode_ST3D_Z_P_BI_Contiguous
                                                                                                                                        msz
                                                                                                                                        imm4
                                                                                                                                        Pg
                                                                                                                                        Rn
                                                                                                                                        Zt)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__2259 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 20)) == (0xE47#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 15
                                                                                                                                                 13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__2258 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__2258 <b 2166) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__2259 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 2166
                                                                                                                                          let msz :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              23
                                                                                                                                              2)
                                                                                                                                          let imm4 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              4)
                                                                                                                                          let Pg :=
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
                                                                                                                                              0
                                                                                                                                              5)
                                                                                                                                          (decode_ST4B_Z_P_BI_Contiguous
                                                                                                                                            msz
                                                                                                                                            imm4
                                                                                                                                            Pg
                                                                                                                                            Rn
                                                                                                                                            Zt)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__2261 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     20)) == (0xE4F#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     15
                                                                                                                                                     13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__2260 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__2260 <b 2167) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__2261 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 2167
                                                                                                                                              let msz :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  23
                                                                                                                                                  2)
                                                                                                                                              let imm4 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  4)
                                                                                                                                              let Pg :=
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
                                                                                                                                                  0
                                                                                                                                                  5)
                                                                                                                                              (decode_ST4H_Z_P_BI_Contiguous
                                                                                                                                                msz
                                                                                                                                                imm4
                                                                                                                                                Pg
                                                                                                                                                Rn
                                                                                                                                                Zt)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__2263 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         20)) == (0xE57#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         15
                                                                                                                                                         13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__2262 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__2262 <b 2168) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__2263 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 2168
                                                                                                                                                  let msz :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      23
                                                                                                                                                      2)
                                                                                                                                                  let imm4 :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      16
                                                                                                                                                      4)
                                                                                                                                                  let Pg :=
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
                                                                                                                                                      0
                                                                                                                                                      5)
                                                                                                                                                  (decode_ST4W_Z_P_BI_Contiguous
                                                                                                                                                    msz
                                                                                                                                                    imm4
                                                                                                                                                    Pg
                                                                                                                                                    Rn
                                                                                                                                                    Zt)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__2265 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             20)) == (0xE5F#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             15
                                                                                                                                                             13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__2264 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__2264 <b 2169) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__2265 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 2169
                                                                                                                                                      let msz :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          23
                                                                                                                                                          2)
                                                                                                                                                      let imm4 :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          16
                                                                                                                                                          4)
                                                                                                                                                      let Pg :=
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
                                                                                                                                                          0
                                                                                                                                                          5)
                                                                                                                                                      (decode_ST4D_Z_P_BI_Contiguous
                                                                                                                                                        msz
                                                                                                                                                        imm4
                                                                                                                                                        Pg
                                                                                                                                                        Rn
                                                                                                                                                        Zt)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__2267 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 20)) == (0xE44#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 15
                                                                                                                                                                 13)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__2266 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__2266 <b 2170) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__2267 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 2170
                                                                                                                                                          let num :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              22
                                                                                                                                                              2)
                                                                                                                                                          let imm4 :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              16
                                                                                                                                                              4)
                                                                                                                                                          let Pg :=
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
                                                                                                                                                              0
                                                                                                                                                              5)
                                                                                                                                                          (decode_ST2Q_Z_P_BI_Contiguous
                                                                                                                                                            num
                                                                                                                                                            imm4
                                                                                                                                                            Pg
                                                                                                                                                            Rn
                                                                                                                                                            Zt)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__2269 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     31
                                                                                                                                                                     20)) == (0xE48#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     15
                                                                                                                                                                     13)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__2268 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__2268 <b 2171) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__2269 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 2171
                                                                                                                                                              let num :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  22
                                                                                                                                                                  2)
                                                                                                                                                              let imm4 :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  16
                                                                                                                                                                  4)
                                                                                                                                                              let Pg :=
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
                                                                                                                                                                  0
                                                                                                                                                                  5)
                                                                                                                                                              (decode_ST3Q_Z_P_BI_Contiguous
                                                                                                                                                                num
                                                                                                                                                                imm4
                                                                                                                                                                Pg
                                                                                                                                                                Rn
                                                                                                                                                                Zt)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__2271 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         31
                                                                                                                                                                         20)) == (0xE4C#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         15
                                                                                                                                                                         13)) == (0b000#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__2270 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__2270 <b 2172) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__2271 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 2172
                                                                                                                                                                  let num :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      22
                                                                                                                                                                      2)
                                                                                                                                                                  let imm4 :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      16
                                                                                                                                                                      4)
                                                                                                                                                                  let Pg :=
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
                                                                                                                                                                      0
                                                                                                                                                                      5)
                                                                                                                                                                  (decode_ST4Q_Z_P_BI_Contiguous
                                                                                                                                                                    num
                                                                                                                                                                    imm4
                                                                                                                                                                    Pg
                                                                                                                                                                    Rn
                                                                                                                                                                    Zt)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__2273 ← (( do
                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             31
                                                                                                                                                                             21)) == (0b10000100000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             15
                                                                                                                                                                             13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__2272 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__2272 <b 2173) : Bool))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false)
                                                                                                                                                                    )
                                                                                                                                                                    :
                                                                                                                                                                    SailM
                                                                                                                                                                    Bool
                                                                                                                                                                    )
                                                                                                                                                                  if (w__2273 : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 2173
                                                                                                                                                                      let msz :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          23
                                                                                                                                                                          2)
                                                                                                                                                                      let Rm :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          16
                                                                                                                                                                          5)
                                                                                                                                                                      let U :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          13
                                                                                                                                                                          1)
                                                                                                                                                                      let Pg :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          10
                                                                                                                                                                          3)
                                                                                                                                                                      let Zn :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          5
                                                                                                                                                                          5)
                                                                                                                                                                      let Zt :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          0
                                                                                                                                                                          5)
                                                                                                                                                                      (decode_LDNT1B_Z_P_AR_S_x32_unscaled
                                                                                                                                                                        msz
                                                                                                                                                                        Rm
                                                                                                                                                                        U
                                                                                                                                                                        Pg
                                                                                                                                                                        Zn
                                                                                                                                                                        Zt)
                                                                                                                                                                      (pure false))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      let w__2275 ← (( do
                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 31
                                                                                                                                                                                 21)) == (0b10000100100#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 15
                                                                                                                                                                                 13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            let w__2274 ← (( do
                                                                                                                                                                              readReg SEE
                                                                                                                                                                              )
                                                                                                                                                                              :
                                                                                                                                                                              SailM
                                                                                                                                                                              Int
                                                                                                                                                                              )
                                                                                                                                                                            (pure (((w__2274 <b 2174) : Bool))))
                                                                                                                                                                        else
                                                                                                                                                                          (pure false)
                                                                                                                                                                        )
                                                                                                                                                                        :
                                                                                                                                                                        SailM
                                                                                                                                                                        Bool
                                                                                                                                                                        )
                                                                                                                                                                      if (w__2275 : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 2174
                                                                                                                                                                          let msz :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              23
                                                                                                                                                                              2)
                                                                                                                                                                          let Rm :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              16
                                                                                                                                                                              5)
                                                                                                                                                                          let U :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              13
                                                                                                                                                                              1)
                                                                                                                                                                          let Pg :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              10
                                                                                                                                                                              3)
                                                                                                                                                                          let Zn :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              5
                                                                                                                                                                              5)
                                                                                                                                                                          let Zt :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              0
                                                                                                                                                                              5)
                                                                                                                                                                          (decode_LDNT1H_Z_P_AR_S_x32_unscaled
                                                                                                                                                                            msz
                                                                                                                                                                            Rm
                                                                                                                                                                            U
                                                                                                                                                                            Pg
                                                                                                                                                                            Zn
                                                                                                                                                                            Zt)
                                                                                                                                                                          (pure false))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          let w__2277 ← (( do
                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     31
                                                                                                                                                                                     21)) == (0b10000101000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     15
                                                                                                                                                                                     13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                                            then
                                                                                                                                                                              (do
                                                                                                                                                                                let w__2276 ← (( do
                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                  )
                                                                                                                                                                                  :
                                                                                                                                                                                  SailM
                                                                                                                                                                                  Int
                                                                                                                                                                                  )
                                                                                                                                                                                (pure (((w__2276 <b 2175) : Bool))))
                                                                                                                                                                            else
                                                                                                                                                                              (pure false)
                                                                                                                                                                            )
                                                                                                                                                                            :
                                                                                                                                                                            SailM
                                                                                                                                                                            Bool
                                                                                                                                                                            )
                                                                                                                                                                          if (w__2277 : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              writeReg SEE 2175
                                                                                                                                                                              let msz :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  23
                                                                                                                                                                                  2)
                                                                                                                                                                              let Rm :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  16
                                                                                                                                                                                  5)
                                                                                                                                                                              let U :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  13
                                                                                                                                                                                  1)
                                                                                                                                                                              let Pg :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  10
                                                                                                                                                                                  3)
                                                                                                                                                                              let Zn :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  5
                                                                                                                                                                                  5)
                                                                                                                                                                              let Zt :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  0
                                                                                                                                                                                  5)
                                                                                                                                                                              (decode_LDNT1W_Z_P_AR_S_x32_unscaled
                                                                                                                                                                                msz
                                                                                                                                                                                Rm
                                                                                                                                                                                U
                                                                                                                                                                                Pg
                                                                                                                                                                                Zn
                                                                                                                                                                                Zt)
                                                                                                                                                                              (pure false))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              let w__2279 ← (( do
                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         31
                                                                                                                                                                                         21)) == (0b10000100000#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         15
                                                                                                                                                                                         13)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                                                then
                                                                                                                                                                                  (do
                                                                                                                                                                                    let w__2278 ← (( do
                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                      )
                                                                                                                                                                                      :
                                                                                                                                                                                      SailM
                                                                                                                                                                                      Int
                                                                                                                                                                                      )
                                                                                                                                                                                    (pure (((w__2278 <b 2176) : Bool))))
                                                                                                                                                                                else
                                                                                                                                                                                  (pure false)
                                                                                                                                                                                )
                                                                                                                                                                                :
                                                                                                                                                                                SailM
                                                                                                                                                                                Bool
                                                                                                                                                                                )
                                                                                                                                                                              if (w__2279 : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  writeReg SEE 2176
                                                                                                                                                                                  let msz :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      23
                                                                                                                                                                                      2)
                                                                                                                                                                                  let Rm :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      16
                                                                                                                                                                                      5)
                                                                                                                                                                                  let U :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      13
                                                                                                                                                                                      1)
                                                                                                                                                                                  let Pg :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      10
                                                                                                                                                                                      3)
                                                                                                                                                                                  let Zn :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      5
                                                                                                                                                                                      5)
                                                                                                                                                                                  let Zt :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      0
                                                                                                                                                                                      5)
                                                                                                                                                                                  (decode_LDNT1SB_Z_P_AR_S_x32_unscaled
                                                                                                                                                                                    msz
                                                                                                                                                                                    Rm
                                                                                                                                                                                    U
                                                                                                                                                                                    Pg
                                                                                                                                                                                    Zn
                                                                                                                                                                                    Zt)
                                                                                                                                                                                  (pure false))
                                                                                                                                                                              else
                                                                                                                                                                                (pure true))))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
